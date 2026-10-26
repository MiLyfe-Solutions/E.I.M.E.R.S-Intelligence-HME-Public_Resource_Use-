import V185TrunkScan23Chunk0385

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2281452 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 3]
def baseStart_2281452 : Nat := 118140960795 + 2281452 * 2 ^ 59
def prefixEnd_2281452 : Nat := 4983230072969 + 3 ^ 40 * 2281452 * 2
def baseEnd_2281452 : Nat := 1171481466161513042257799

theorem tailTrace_2281452 : CollatzResearch.WordTrace tailWord_2281452 prefixEnd_2281452 1171481466161513042257799 := by
  unfold tailWord_2281452
  simp only [CollatzResearch.WordTrace]
  refine ⟨41605695265348259912903305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55474260353797679883871073 41605695265348259912903305)
  ·
    refine ⟨31204271449011194934677479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41605695265348259912903305 31204271449011194934677479)
    ·
      refine ⟨46806407173516792402016219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31204271449011194934677479 46806407173516792402016219)
      ·
        refine ⟨70209610760275188603024329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46806407173516792402016219 70209610760275188603024329)
        ·
          refine ⟨52657208070206391452268247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70209610760275188603024329 52657208070206391452268247)
          ·
            refine ⟨78985812105309587178402371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52657208070206391452268247 78985812105309587178402371)
            ·
              refine ⟨118478718157964380767603557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78985812105309587178402371 118478718157964380767603557)
              ·
                refine ⟨22214759654618321393925667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118478718157964380767603557 22214759654618321393925667)
                ·
                  refine ⟨33322139481927482090888501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22214759654618321393925667 33322139481927482090888501)
                  ·
                    refine ⟨3123950576430701446020797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33322139481927482090888501 3123950576430701446020797)
                    ·
                      refine ⟨1171481466161513042257799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3123950576430701446020797 1171481466161513042257799)
                      ·
                        rfl

theorem cell23_2281452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_2281452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281452 prefixEnd_2281452 := by exact prefixLift 2281452
  have htrace : WordTrace (prefixWord ++ tailWord_2281452) baseStart_2281452 baseEnd_2281452 := by
    simpa [prefixWord, tailWord_2281452, baseEnd_2281452] using wordTrace_append hprefix tailTrace_2281452
  have hstable : (prefixWord ++ tailWord_2281452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281452).length < 2 ^ (prefixWord ++ tailWord_2281452).sum := by decide
  have hdescent : baseEnd_2281452 < baseStart_2281452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281509 : List Nat := [1, 3, 1, 2, 2, 3, 1, 3, 2, 1, 4]
def baseStart_2281509 : Nat := 118140960795 + 2281509 * 2 ^ 59
def prefixEnd_2281509 : Nat := 4983230072969 + 3 ^ 40 * 2281509 * 2
def baseEnd_2281509 : Nat := 1171510734558819319245037

theorem tailTrace_2281509 : CollatzResearch.WordTrace tailWord_2281509 prefixEnd_2281509 1171510734558819319245037 := by
  unfold tailWord_2281509
  simp only [CollatzResearch.WordTrace]
  refine ⟨83213469491490018560631581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55475646327660012373754387 83213469491490018560631581)
  ·
    refine ⟨31205051059308756960236843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83213469491490018560631581 31205051059308756960236843)
    ·
      refine ⟨46807576588963135440355265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31205051059308756960236843 46807576588963135440355265)
      ·
        refine ⟨35105682441722351580266449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46807576588963135440355265 35105682441722351580266449)
        ·
          refine ⟨26329261831291763685199837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35105682441722351580266449 26329261831291763685199837)
          ·
            refine ⟨9873473186734411381949939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26329261831291763685199837 9873473186734411381949939)
            ·
              refine ⟨14810209780101617072924909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9873473186734411381949939 14810209780101617072924909)
              ·
                refine ⟨5553828667538106402346841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14810209780101617072924909 5553828667538106402346841)
                ·
                  refine ⟨4165371500653579801760131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5553828667538106402346841 4165371500653579801760131)
                  ·
                    refine ⟨6248057250980369702640197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4165371500653579801760131 6248057250980369702640197)
                    ·
                      refine ⟨1171510734558819319245037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6248057250980369702640197 1171510734558819319245037)
                      ·
                        rfl

theorem cell23_2281509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_2281509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281509 prefixEnd_2281509 := by exact prefixLift 2281509
  have htrace : WordTrace (prefixWord ++ tailWord_2281509) baseStart_2281509 baseEnd_2281509 := by
    simpa [prefixWord, tailWord_2281509, baseEnd_2281509] using wordTrace_append hprefix tailTrace_2281509
  have hstable : (prefixWord ++ tailWord_2281509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281509).length < 2 ^ (prefixWord ++ tailWord_2281509).sum := by decide
  have hdescent : baseEnd_2281509 < baseStart_2281509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281526 : List Nat := [5, 1, 2, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_2281526 : Nat := 118140960795 + 2281526 * 2 ^ 59
def prefixEnd_2281526 : Nat := 4983230072969 + 3 ^ 40 * 2281526 * 2
def baseEnd_2281526 : Nat := 1171519463729945752732459

theorem tailTrace_2281526 : CollatzResearch.WordTrace tailWord_2281526 prefixEnd_2281526 1171519463729945752732459 := by
  unfold tailWord_2281526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5200880595776776904000027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55476059688285620309333621 5200880595776776904000027)
  ·
    refine ⟨7801320893665165356000041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5200880595776776904000027 7801320893665165356000041)
    ·
      refine ⟨5850990670248874017000031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7801320893665165356000041 5850990670248874017000031)
      ·
        refine ⟨8776486005373311025500047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5850990670248874017000031 8776486005373311025500047)
        ·
          refine ⟨13164729008059966538250071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8776486005373311025500047 13164729008059966538250071)
          ·
            refine ⟨19747093512089949807375107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13164729008059966538250071 19747093512089949807375107)
            ·
              refine ⟨29620640268134924711062661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19747093512089949807375107 29620640268134924711062661)
              ·
                refine ⟨5553870050275298383324249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29620640268134924711062661 5553870050275298383324249)
                ·
                  refine ⟨4165402537706473787493187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5553870050275298383324249 4165402537706473787493187)
                  ·
                    refine ⟨6248103806559710681239781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4165402537706473787493187 6248103806559710681239781)
                    ·
                      refine ⟨1171519463729945752732459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6248103806559710681239781 1171519463729945752732459)
                      ·
                        rfl

theorem cell23_2281526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_2281526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281526 prefixEnd_2281526 := by exact prefixLift 2281526
  have htrace : WordTrace (prefixWord ++ tailWord_2281526) baseStart_2281526 baseEnd_2281526 := by
    simpa [prefixWord, tailWord_2281526, baseEnd_2281526] using wordTrace_append hprefix tailTrace_2281526
  have hstable : (prefixWord ++ tailWord_2281526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281526).length < 2 ^ (prefixWord ++ tailWord_2281526).sum := by decide
  have hdescent : baseEnd_2281526 < baseStart_2281526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281593 : List Nat := [1, 2, 1, 3, 4, 2, 2, 1, 3, 1, 3]
def baseStart_2281593 : Nat := 118140960795 + 2281593 * 2 ^ 59
def prefixEnd_2281593 : Nat := 4983230072969 + 3 ^ 40 * 2281593 * 2
def baseEnd_2281593 : Nat := 1171553866933796990594651

theorem tailTrace_2281593 : CollatzResearch.WordTrace tailWord_2281593 prefixEnd_2281593 1171553866933796990594651 := by
  unfold tailWord_2281593
  simp only [CollatzResearch.WordTrace]
  refine ⟨83216533223185700906689433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55477688815457133937792955 83216533223185700906689433)
  ·
    refine ⟨62412399917389275680017075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83216533223185700906689433 62412399917389275680017075)
    ·
      refine ⟨93618599876083913520025613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62412399917389275680017075 93618599876083913520025613)
      ·
        refine ⟨35106974953531467570009605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93618599876083913520025613 35106974953531467570009605)
        ·
          refine ⟨6582557803787150169376801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35106974953531467570009605 6582557803787150169376801)
          ·
            refine ⟨4936918352840362627032601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6582557803787150169376801 4936918352840362627032601)
            ·
              refine ⟨3702688764630271970274451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4936918352840362627032601 3702688764630271970274451)
              ·
                refine ⟨5554033146945407955411677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3702688764630271970274451 5554033146945407955411677)
                ·
                  refine ⟨2082762430104527983279379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5554033146945407955411677 2082762430104527983279379)
                  ·
                    refine ⟨3124143645156791974919069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2082762430104527983279379 3124143645156791974919069)
                    ·
                      refine ⟨1171553866933796990594651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3124143645156791974919069 1171553866933796990594651)
                      ·
                        rfl

theorem cell23_2281593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_2281593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281593 prefixEnd_2281593 := by exact prefixLift 2281593
  have htrace : WordTrace (prefixWord ++ tailWord_2281593) baseStart_2281593 baseEnd_2281593 := by
    simpa [prefixWord, tailWord_2281593, baseEnd_2281593] using wordTrace_append hprefix tailTrace_2281593
  have hstable : (prefixWord ++ tailWord_2281593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281593).length < 2 ^ (prefixWord ++ tailWord_2281593).sum := by decide
  have hdescent : baseEnd_2281593 < baseStart_2281593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281616 : List Nat := [2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 4]
def baseStart_2281616 : Nat := 118140960795 + 2281616 * 2 ^ 59
def prefixEnd_2281616 : Nat := 4983230072969 + 3 ^ 40 * 2281616 * 2
def baseEnd_2281616 : Nat := 1171565676988850400607045

theorem tailTrace_2281616 : CollatzResearch.WordTrace tailWord_2281616 prefixEnd_2281616 1171565676988850400607045 := by
  unfold tailWord_2281616
  simp only [CollatzResearch.WordTrace]
  refine ⟨41608686051051187917388351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55478248068068250556517801 41608686051051187917388351)
  ·
    refine ⟨62413029076576781876082527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41608686051051187917388351 62413029076576781876082527)
    ·
      refine ⟨93619543614865172814123791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62413029076576781876082527 93619543614865172814123791)
      ·
        refine ⟨140429315422297759221185687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93619543614865172814123791 140429315422297759221185687)
        ·
          refine ⟨210643973133446638831778531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140429315422297759221185687 210643973133446638831778531)
          ·
            refine ⟨315965959700169958247667797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210643973133446638831778531 315965959700169958247667797)
            ·
              refine ⟨3702726090236366698214857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 315965959700169958247667797 3702726090236366698214857)
              ·
                refine ⟨2777044567677275023661143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3702726090236366698214857 2777044567677275023661143)
                ·
                  refine ⟨4165566851515912535491715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2777044567677275023661143 4165566851515912535491715)
                  ·
                    refine ⟨6248350277273868803237573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4165566851515912535491715 6248350277273868803237573)
                    ·
                      refine ⟨1171565676988850400607045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6248350277273868803237573 1171565676988850400607045)
                      ·
                        rfl

theorem cell23_2281616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 4].length) (baseStart_2281616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281616 prefixEnd_2281616 := by exact prefixLift 2281616
  have htrace : WordTrace (prefixWord ++ tailWord_2281616) baseStart_2281616 baseEnd_2281616 := by
    simpa [prefixWord, tailWord_2281616, baseEnd_2281616] using wordTrace_append hprefix tailTrace_2281616
  have hstable : (prefixWord ++ tailWord_2281616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281616).length < 2 ^ (prefixWord ++ tailWord_2281616).sum := by decide
  have hdescent : baseEnd_2281616 < baseStart_2281616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281757 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 4, 2, 2]
def baseStart_2281757 : Nat := 118140960795 + 2281757 * 2 ^ 59
def prefixEnd_2281757 : Nat := 4983230072969 + 3 ^ 40 * 2281757 * 2
def baseEnd_2281757 : Nat := 1171638077761134348943897

theorem tailTrace_2281757 : CollatzResearch.WordTrace tailWord_2281757 prefixEnd_2281757 1171638077761134348943897 := by
  unfold tailWord_2281757
  simp only [CollatzResearch.WordTrace]
  refine ⟨83222514794591556915659525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55481676529727704610439683 83222514794591556915659525)
  ·
    refine ⟨15604221523985916921686161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83222514794591556915659525 15604221523985916921686161)
    ·
      refine ⟨11703166142989437691264621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15604221523985916921686161 11703166142989437691264621)
      ·
        refine ⟨4388687303621039134224233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11703166142989437691264621 4388687303621039134224233)
        ·
          refine ⟨3291515477715779350668175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4388687303621039134224233 3291515477715779350668175)
          ·
            refine ⟨4937273216573669026002263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3291515477715779350668175 4937273216573669026002263)
            ·
              refine ⟨7405909824860503539003395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4937273216573669026002263 7405909824860503539003395)
              ·
                refine ⟨11108864737290755308505093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7405909824860503539003395 11108864737290755308505093)
                ·
                  refine ⟨2082912138242016620344705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11108864737290755308505093 2082912138242016620344705)
                  ·
                    refine ⟨1562184103681512465258529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2082912138242016620344705 1562184103681512465258529)
                    ·
                      refine ⟨1171638077761134348943897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1562184103681512465258529 1171638077761134348943897)
                      ·
                        rfl

theorem cell23_2281757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_2281757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281757 prefixEnd_2281757 := by exact prefixLift 2281757
  have htrace : WordTrace (prefixWord ++ tailWord_2281757) baseStart_2281757 baseEnd_2281757 := by
    simpa [prefixWord, tailWord_2281757, baseEnd_2281757] using wordTrace_append hprefix tailTrace_2281757
  have hstable : (prefixWord ++ tailWord_2281757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281757).length < 2 ^ (prefixWord ++ tailWord_2281757).sum := by decide
  have hdescent : baseEnd_2281757 < baseStart_2281757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281774 : List Nat := [4, 1, 3, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_2281774 : Nat := 118140960795 + 2281774 * 2 ^ 59
def prefixEnd_2281774 : Nat := 4983230072969 + 3 ^ 40 * 2281774 * 2
def baseEnd_2281774 : Nat := 1171646806932260782431319

theorem tailTrace_2281774 : CollatzResearch.WordTrace tailWord_2281774 prefixEnd_2281774 1171646806932260782431319 := by
  unfold tailWord_2281774
  simp only [CollatzResearch.WordTrace]
  refine ⟨10402891854441246102378547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55482089890353312546018917 10402891854441246102378547)
  ·
    refine ⟨15604337781661869153567821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10402891854441246102378547 15604337781661869153567821)
    ·
      refine ⟨5851626668123200932587933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15604337781661869153567821 5851626668123200932587933)
      ·
        refine ⟨2194360000546200349720475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5851626668123200932587933 2194360000546200349720475)
        ·
          refine ⟨3291540000819300524580713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2194360000546200349720475 3291540000819300524580713)
          ·
            refine ⟨2468655000614475393435535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3291540000819300524580713 2468655000614475393435535)
            ·
              refine ⟨3702982500921713090153303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2468655000614475393435535 3702982500921713090153303)
              ·
                refine ⟨5554473751382569635229955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3702982500921713090153303 5554473751382569635229955)
                ·
                  refine ⟨8331710627073854452844933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5554473751382569635229955 8331710627073854452844933)
                  ·
                    refine ⟨1562195742576347709908425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8331710627073854452844933 1562195742576347709908425)
                    ·
                      refine ⟨1171646806932260782431319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1562195742576347709908425 1171646806932260782431319)
                      ·
                        rfl

theorem cell23_2281774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_2281774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281774 prefixEnd_2281774 := by exact prefixLift 2281774
  have htrace : WordTrace (prefixWord ++ tailWord_2281774) baseStart_2281774 baseEnd_2281774 := by
    simpa [prefixWord, tailWord_2281774, baseEnd_2281774] using wordTrace_append hprefix tailTrace_2281774
  have hstable : (prefixWord ++ tailWord_2281774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281774).length < 2 ^ (prefixWord ++ tailWord_2281774).sum := by decide
  have hdescent : baseEnd_2281774 < baseStart_2281774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281816 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 3, 4, 3]
def baseStart_2281816 : Nat := 118140960795 + 2281816 * 2 ^ 59
def prefixEnd_2281816 : Nat := 4983230072969 + 3 ^ 40 * 2281816 * 2
def baseEnd_2281816 : Nat := 1171668373119749618106125

theorem tailTrace_2281816 : CollatzResearch.WordTrace tailWord_2281816 prefixEnd_2281816 1171668373119749618106125 := by
  unfold tailWord_2281816
  simp only [CollatzResearch.WordTrace]
  refine ⟨41612333350688904996028651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55483111134251873328038201 41612333350688904996028651)
  ·
    refine ⟨62418500026033357494042977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41612333350688904996028651 62418500026033357494042977)
    ·
      refine ⟨46813875019525018120532233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62418500026033357494042977 46813875019525018120532233)
      ·
        refine ⟨35110406264643763590399175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46813875019525018120532233 35110406264643763590399175)
        ·
          refine ⟨52665609396965645385598763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35110406264643763590399175 52665609396965645385598763)
          ·
            refine ⟨78998414095448468078398145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52665609396965645385598763 78998414095448468078398145)
            ·
              refine ⟨59248810571586351058798609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78998414095448468078398145 59248810571586351058798609)
              ·
                refine ⟨44436607928689763294098957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59248810571586351058798609 44436607928689763294098957)
                ·
                  refine ⟨16663727973258661235287109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44436607928689763294098957 16663727973258661235287109)
                  ·
                    refine ⟨3124448994985998981616333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16663727973258661235287109 3124448994985998981616333)
                    ·
                      refine ⟨1171668373119749618106125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3124448994985998981616333 1171668373119749618106125)
                      ·
                        rfl

theorem cell23_2281816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_2281816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281816 prefixEnd_2281816 := by exact prefixLift 2281816
  have htrace : WordTrace (prefixWord ++ tailWord_2281816) baseStart_2281816 baseEnd_2281816 := by
    simpa [prefixWord, tailWord_2281816, baseEnd_2281816] using wordTrace_append hprefix tailTrace_2281816
  have hstable : (prefixWord ++ tailWord_2281816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281816).length < 2 ^ (prefixWord ++ tailWord_2281816).sum := by decide
  have hdescent : baseEnd_2281816 < baseStart_2281816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281820 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_2281820 : Nat := 118140960795 + 2281820 * 2 ^ 59
def prefixEnd_2281820 : Nat := 4983230072969 + 3 ^ 40 * 2281820 * 2
def baseEnd_2281820 : Nat := 1171670427042367602456107

theorem tailTrace_2281820 : CollatzResearch.WordTrace tailWord_2281820 prefixEnd_2281820 1171670427042367602456107 := by
  unfold tailWord_2281820
  simp only [CollatzResearch.WordTrace]
  refine ⟨41612406296681659337601457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55483208395575545783468609 41612406296681659337601457)
  ·
    refine ⟨31209304722511244503201093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41612406296681659337601457 31209304722511244503201093)
    ·
      refine ⟨5851744635470858344350205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31209304722511244503201093 5851744635470858344350205)
      ·
        refine ⟨2194404238301571879131327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5851744635470858344350205 2194404238301571879131327)
        ·
          refine ⟨3291606357452357818696991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2194404238301571879131327 3291606357452357818696991)
          ·
            refine ⟨4937409536178536728045487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3291606357452357818696991 4937409536178536728045487)
            ·
              refine ⟨7406114304267805092068231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4937409536178536728045487 7406114304267805092068231)
              ·
                refine ⟨11109171456401707638102347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7406114304267805092068231 11109171456401707638102347)
                ·
                  refine ⟨16663757184602561457153521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11109171456401707638102347 16663757184602561457153521)
                  ·
                    refine ⟨12497817888451921092865141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16663757184602561457153521 12497817888451921092865141)
                    ·
                      refine ⟨1171670427042367602456107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12497817888451921092865141 1171670427042367602456107)
                      ·
                        rfl

theorem cell23_2281820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_2281820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281820 prefixEnd_2281820 := by exact prefixLift 2281820
  have htrace : WordTrace (prefixWord ++ tailWord_2281820) baseStart_2281820 baseEnd_2281820 := by
    simpa [prefixWord, tailWord_2281820, baseEnd_2281820] using wordTrace_append hprefix tailTrace_2281820
  have hstable : (prefixWord ++ tailWord_2281820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281820).length < 2 ^ (prefixWord ++ tailWord_2281820).sum := by decide
  have hdescent : baseEnd_2281820 < baseStart_2281820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281823 : List Nat := [1, 1, 2, 3, 1, 2, 5, 1, 3, 4]
def baseStart_2281823 : Nat := 118140960795 + 2281823 * 2 ^ 59
def prefixEnd_2281823 : Nat := 4983230072969 + 3 ^ 40 * 2281823 * 2
def baseEnd_2281823 : Nat := 390557322494777030239531

theorem tailTrace_2281823 : CollatzResearch.WordTrace tailWord_2281823 prefixEnd_2281823 390557322494777030239531 := by
  unfold tailWord_2281823
  simp only [CollatzResearch.WordTrace]
  refine ⟨83224922012352450187562123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55483281341568300125041415 83224922012352450187562123)
  ·
    refine ⟨124837383018528675281343185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83224922012352450187562123 124837383018528675281343185)
    ·
      refine ⟨93628037263896506461007389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124837383018528675281343185 93628037263896506461007389)
      ·
        refine ⟨35110513973961189922877771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93628037263896506461007389 35110513973961189922877771)
        ·
          refine ⟨52665770960941784884316657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35110513973961189922877771 52665770960941784884316657)
          ·
            refine ⟨39499328220706338663237493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52665770960941784884316657 39499328220706338663237493)
            ·
              refine ⟨3703062020691219249678515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39499328220706338663237493 3703062020691219249678515)
              ·
                refine ⟨5554593031036828874517773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3703062020691219249678515 5554593031036828874517773)
                ·
                  refine ⟨2082972386638810827944165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5554593031036828874517773 2082972386638810827944165)
                  ·
                    refine ⟨390557322494777030239531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2082972386638810827944165 390557322494777030239531)
                    ·
                      rfl

theorem cell23_2281823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 4].length) (baseStart_2281823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281823 prefixEnd_2281823 := by exact prefixLift 2281823
  have htrace : WordTrace (prefixWord ++ tailWord_2281823) baseStart_2281823 baseEnd_2281823 := by
    simpa [prefixWord, tailWord_2281823, baseEnd_2281823] using wordTrace_append hprefix tailTrace_2281823
  have hstable : (prefixWord ++ tailWord_2281823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281823).length < 2 ^ (prefixWord ++ tailWord_2281823).sum := by decide
  have hdescent : baseEnd_2281823 < baseStart_2281823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281870 : List Nat := [4, 1, 1, 4, 1, 2, 2, 2, 6]
def baseStart_2281870 : Nat := 118140960795 + 2281870 * 2 ^ 59
def prefixEnd_2281870 : Nat := 4983230072969 + 3 ^ 40 * 2281870 * 2
def baseEnd_2281870 : Nat := 130188455675010267425653

theorem tailTrace_2281870 : CollatzResearch.WordTrace tailWord_2281870 prefixEnd_2281870 130188455675010267425653 := by
  unfold tailWord_2281870
  simp only [CollatzResearch.WordTrace]
  refine ⟨10403329530397772151815383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55484424162121451476348709 10403329530397772151815383)
  ·
    refine ⟨15604994295596658227723075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10403329530397772151815383 15604994295596658227723075)
    ·
      refine ⟨23407491443394987341584613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15604994295596658227723075 23407491443394987341584613)
      ·
        refine ⟨4388904645636560126547115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23407491443394987341584613 4388904645636560126547115)
        ·
          refine ⟨6583356968454840189820673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4388904645636560126547115 6583356968454840189820673)
          ·
            refine ⟨4937517726341130142365505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6583356968454840189820673 4937517726341130142365505)
            ·
              refine ⟨3703138294755847606774129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4937517726341130142365505 3703138294755847606774129)
              ·
                refine ⟨2777353721066885705080597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3703138294755847606774129 2777353721066885705080597)
                ·
                  refine ⟨130188455675010267425653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2777353721066885705080597 130188455675010267425653)
                  ·
                    rfl

theorem cell23_2281870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_2281870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281870 prefixEnd_2281870 := by exact prefixLift 2281870
  have htrace : WordTrace (prefixWord ++ tailWord_2281870) baseStart_2281870 baseEnd_2281870 := by
    simpa [prefixWord, tailWord_2281870, baseEnd_2281870] using wordTrace_append hprefix tailTrace_2281870
  have hstable : (prefixWord ++ tailWord_2281870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281870).length < 2 ^ (prefixWord ++ tailWord_2281870).sum := by decide
  have hdescent : baseEnd_2281870 < baseStart_2281870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281890 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 1, 5, 2]
def baseStart_2281890 : Nat := 118140960795 + 2281890 * 2 ^ 59
def prefixEnd_2281890 : Nat := 4983230072969 + 3 ^ 40 * 2281890 * 2
def baseEnd_2281890 : Nat := 1171706370688182328580785

theorem tailTrace_2281890 : CollatzResearch.WordTrace tailWord_2281890 prefixEnd_2281890 1171706370688182328580785 := by
  unfold tailWord_2281890
  simp only [CollatzResearch.WordTrace]
  refine ⟨20806841425777430157562781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55484910468739813753500749 20806841425777430157562781)
  ·
    refine ⟨7802565534666536309086043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20806841425777430157562781 7802565534666536309086043)
    ·
      refine ⟨11703848301999804463629065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7802565534666536309086043 11703848301999804463629065)
      ·
        refine ⟨8777886226499853347721799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11703848301999804463629065 8777886226499853347721799)
        ·
          refine ⟨13166829339749780021582699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8777886226499853347721799 13166829339749780021582699)
          ·
            refine ⟨19750244009624670032374049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13166829339749780021582699 19750244009624670032374049)
            ·
              refine ⟨14812683007218502524280537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19750244009624670032374049 14812683007218502524280537)
              ·
                refine ⟨11109512255413876893210403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14812683007218502524280537 11109512255413876893210403)
                ·
                  refine ⟨16664268383120815339815605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11109512255413876893210403 16664268383120815339815605)
                  ·
                    refine ⟨1562275160917576438107713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16664268383120815339815605 1562275160917576438107713)
                    ·
                      refine ⟨1171706370688182328580785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1562275160917576438107713 1171706370688182328580785)
                      ·
                        rfl

theorem cell23_2281890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_2281890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281890 prefixEnd_2281890 := by exact prefixLift 2281890
  have htrace : WordTrace (prefixWord ++ tailWord_2281890) baseStart_2281890 baseEnd_2281890 := by
    simpa [prefixWord, tailWord_2281890, baseEnd_2281890] using wordTrace_append hprefix tailTrace_2281890
  have hstable : (prefixWord ++ tailWord_2281890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281890).length < 2 ^ (prefixWord ++ tailWord_2281890).sum := by decide
  have hdescent : baseEnd_2281890 < baseStart_2281890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281913 : List Nat := [1, 2, 1, 4, 3, 1, 2, 2, 1, 6]
def baseStart_2281913 : Nat := 118140960795 + 2281913 * 2 ^ 59
def prefixEnd_2281913 : Nat := 4983230072969 + 3 ^ 40 * 2281913 * 2
def baseEnd_2281913 : Nat := 390572726914411912864393

theorem tailTrace_2281913 : CollatzResearch.WordTrace tailWord_2281913 prefixEnd_2281913 390572726914411912864393 := by
  unfold tailWord_2281913
  simp only [CollatzResearch.WordTrace]
  refine ⟨83228204582026395558338393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55485469721350930372225595 83228204582026395558338393)
  ·
    refine ⟨62421153436519796668753795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83228204582026395558338393 62421153436519796668753795)
    ·
      refine ⟨93631730154779695003130693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62421153436519796668753795 93631730154779695003130693)
      ·
        refine ⟨17555949404021192813087005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93631730154779695003130693 17555949404021192813087005)
        ·
          refine ⟨6583481026507947304907627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17555949404021192813087005 6583481026507947304907627)
          ·
            refine ⟨9875221539761920957361441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6583481026507947304907627 9875221539761920957361441)
            ·
              refine ⟨7406416154821440718021081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9875221539761920957361441 7406416154821440718021081)
              ·
                refine ⟨5554812116116080538515811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7406416154821440718021081 5554812116116080538515811)
                ·
                  refine ⟨8332218174174120807773717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5554812116116080538515811 8332218174174120807773717)
                  ·
                    refine ⟨390572726914411912864393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8332218174174120807773717 390572726914411912864393)
                    ·
                      rfl

theorem cell23_2281913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 6].length) (baseStart_2281913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281913 prefixEnd_2281913 := by exact prefixLift 2281913
  have htrace : WordTrace (prefixWord ++ tailWord_2281913) baseStart_2281913 baseEnd_2281913 := by
    simpa [prefixWord, tailWord_2281913, baseEnd_2281913] using wordTrace_append hprefix tailTrace_2281913
  have hstable : (prefixWord ++ tailWord_2281913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281913).length < 2 ^ (prefixWord ++ tailWord_2281913).sum := by decide
  have hdescent : baseEnd_2281913 < baseStart_2281913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281917 : List Nat := [1, 4, 1, 2, 2, 4, 2, 1, 1, 5]
def baseStart_2281917 : Nat := 118140960795 + 2281917 * 2 ^ 59
def prefixEnd_2281917 : Nat := 4983230072969 + 3 ^ 40 * 2281917 * 2
def baseEnd_2281917 : Nat := 390573411555284574314387

theorem tailTrace_2281917 : CollatzResearch.WordTrace tailWord_2281917 prefixEnd_2281917 390573411555284574314387 := by
  unfold tailWord_2281917
  simp only [CollatzResearch.WordTrace]
  refine ⟨83228350474011904241484005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55485566982674602827656003 83228350474011904241484005)
  ·
    refine ⟨15605315713877232045278251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83228350474011904241484005 15605315713877232045278251)
    ·
      refine ⟨23407973570815848067917377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15605315713877232045278251 23407973570815848067917377)
      ·
        refine ⟨17555980178111886050938033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23407973570815848067917377 17555980178111886050938033)
        ·
          refine ⟨13166985133583914538203525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17555980178111886050938033 13166985133583914538203525)
          ·
            refine ⟨2468809712546983975913161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13166985133583914538203525 2468809712546983975913161)
            ·
              refine ⟨1851607284410237981934871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2468809712546983975913161 1851607284410237981934871)
              ·
                refine ⟨2777410926615356972902307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1851607284410237981934871 2777410926615356972902307)
                ·
                  refine ⟨4166116389923035459353461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2777410926615356972902307 4166116389923035459353461)
                  ·
                    refine ⟨390573411555284574314387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4166116389923035459353461 390573411555284574314387)
                    ·
                      rfl

theorem cell23_2281917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_2281917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281917 prefixEnd_2281917 := by exact prefixLift 2281917
  have htrace : WordTrace (prefixWord ++ tailWord_2281917) baseStart_2281917 baseEnd_2281917 := by
    simpa [prefixWord, tailWord_2281917, baseEnd_2281917] using wordTrace_append hprefix tailTrace_2281917
  have hstable : (prefixWord ++ tailWord_2281917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281917).length < 2 ^ (prefixWord ++ tailWord_2281917).sum := by decide
  have hdescent : baseEnd_2281917 < baseStart_2281917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281920 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 7, 2, 2]
def baseStart_2281920 : Nat := 118140960795 + 2281920 * 2 ^ 59
def prefixEnd_2281920 : Nat := 4983230072969 + 3 ^ 40 * 2281920 * 2
def baseEnd_2281920 : Nat := 1171721775107817211205647

theorem tailTrace_2281920 : CollatzResearch.WordTrace tailWord_2281920 prefixEnd_2281920 1171721775107817211205647 := by
  unfold tailWord_2281920
  simp only [CollatzResearch.WordTrace]
  refine ⟨41614229946500517876921607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55485639928667357169228809 41614229946500517876921607)
  ·
    refine ⟨62421344919750776815382411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41614229946500517876921607 62421344919750776815382411)
    ·
      refine ⟨93632017379626165223073617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62421344919750776815382411 93632017379626165223073617)
      ·
        refine ⟨70224013034719623917305213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93632017379626165223073617 70224013034719623917305213)
        ·
          refine ⟨26334004888019858968989455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70224013034719623917305213 26334004888019858968989455)
          ·
            refine ⟨39501007332029788453484183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26334004888019858968989455 39501007332029788453484183)
            ·
              refine ⟨59251510998044682680226275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39501007332029788453484183 59251510998044682680226275)
              ·
                refine ⟨88877266497067024020339413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59251510998044682680226275 88877266497067024020339413)
                ·
                  refine ⟨2083060933525008375476705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 88877266497067024020339413 2083060933525008375476705)
                  ·
                    refine ⟨1562295700143756281607529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2083060933525008375476705 1562295700143756281607529)
                    ·
                      refine ⟨1171721775107817211205647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1562295700143756281607529 1171721775107817211205647)
                      ·
                        rfl

theorem cell23_2281920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 7, 2, 2].length) (baseStart_2281920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281920 prefixEnd_2281920 := by exact prefixLift 2281920
  have htrace : WordTrace (prefixWord ++ tailWord_2281920) baseStart_2281920 baseEnd_2281920 := by
    simpa [prefixWord, tailWord_2281920, baseEnd_2281920] using wordTrace_append hprefix tailTrace_2281920
  have hstable : (prefixWord ++ tailWord_2281920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281920).length < 2 ^ (prefixWord ++ tailWord_2281920).sum := by decide
  have hdescent : baseEnd_2281920 < baseStart_2281920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281921 : List Nat := [1, 2, 7, 1, 2, 1, 1, 2, 6]
def baseStart_2281921 : Nat := 118140960795 + 2281921 * 2 ^ 59
def prefixEnd_2281921 : Nat := 4983230072969 + 3 ^ 40 * 2281921 * 2
def baseEnd_2281921 : Nat := 130191365398719078588127

theorem tailTrace_2281921 : CollatzResearch.WordTrace tailWord_2281921 prefixEnd_2281921 130191365398719078588127 := by
  unfold tailWord_2281921
  simp only [CollatzResearch.WordTrace]
  refine ⟨83228496365997412924629617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55485664243998275283086411 83228496365997412924629617)
  ·
    refine ⟨62421372274498059693472213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83228496365997412924629617 62421372274498059693472213)
    ·
      refine ⟨1463000912683548274065755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 62421372274498059693472213 1463000912683548274065755)
      ·
        refine ⟨2194501369025322411098633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1463000912683548274065755 2194501369025322411098633)
        ·
          refine ⟨1645876026768991808323975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2194501369025322411098633 1645876026768991808323975)
          ·
            refine ⟨2468814040153487712485963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645876026768991808323975 2468814040153487712485963)
            ·
              refine ⟨3703221060230231568728945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2468814040153487712485963 3703221060230231568728945)
              ·
                refine ⟨2777415795172673676546709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3703221060230231568728945 2777415795172673676546709)
                ·
                  refine ⟨130191365398719078588127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2777415795172673676546709 130191365398719078588127)
                  ·
                    rfl

theorem cell23_2281921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 6].length) (baseStart_2281921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281921 prefixEnd_2281921 := by exact prefixLift 2281921
  have htrace : WordTrace (prefixWord ++ tailWord_2281921) baseStart_2281921 baseEnd_2281921 := by
    simpa [prefixWord, tailWord_2281921, baseEnd_2281921] using wordTrace_append hprefix tailTrace_2281921
  have hstable : (prefixWord ++ tailWord_2281921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281921).length < 2 ^ (prefixWord ++ tailWord_2281921).sum := by decide
  have hdescent : baseEnd_2281921 < baseStart_2281921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281940 : List Nat := [2, 4, 1, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_2281940 : Nat := 118140960795 + 2281940 * 2 ^ 59
def prefixEnd_2281940 : Nat := 4983230072969 + 3 ^ 40 * 2281940 * 2
def baseEnd_2281940 : Nat := 1171732044720907132955555

theorem tailTrace_2281940 : CollatzResearch.WordTrace tailWord_2281940 prefixEnd_2281940 1171732044720907132955555 := by
  unfold tailWord_2281940
  simp only [CollatzResearch.WordTrace]
  refine ⟨41614594676464289584785637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55486126235285719446380849 41614594676464289584785637)
  ·
    refine ⟨7802736501837054297147307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41614594676464289584785637 7802736501837054297147307)
    ·
      refine ⟨11704104752755581445720961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7802736501837054297147307 11704104752755581445720961)
      ·
        refine ⟨8778078564566686084290721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11704104752755581445720961 8778078564566686084290721)
        ·
          refine ⟨6583558923425014563218041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8778078564566686084290721 6583558923425014563218041)
          ·
            refine ⟨4937669192568760922413531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6583558923425014563218041 4937669192568760922413531)
            ·
              refine ⟨7406503788853141383620297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4937669192568760922413531 7406503788853141383620297)
              ·
                refine ⟨5554877841639856037715223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7406503788853141383620297 5554877841639856037715223)
                ·
                  refine ⟨8332316762459784056572835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5554877841639856037715223 8332316762459784056572835)
                  ·
                    refine ⟨12498475143689676084859253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8332316762459784056572835 12498475143689676084859253)
                    ·
                      refine ⟨1171732044720907132955555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12498475143689676084859253 1171732044720907132955555)
                      ·
                        rfl

theorem cell23_2281940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_2281940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281940 prefixEnd_2281940 := by exact prefixLift 2281940
  have htrace : WordTrace (prefixWord ++ tailWord_2281940) baseStart_2281940 baseEnd_2281940 := by
    simpa [prefixWord, tailWord_2281940, baseEnd_2281940] using wordTrace_append hprefix tailTrace_2281940
  have hstable : (prefixWord ++ tailWord_2281940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281940).length < 2 ^ (prefixWord ++ tailWord_2281940).sum := by decide
  have hdescent : baseEnd_2281940 < baseStart_2281940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281960 : List Nat := [2, 1, 4, 1, 1, 5, 2, 7]
def baseStart_2281960 : Nat := 118140960795 + 2281960 * 2 ^ 59
def prefixEnd_2281960 : Nat := 4983230072969 + 3 ^ 40 * 2281960 * 2
def baseEnd_2281960 : Nat := 43397863493851742766869

theorem tailTrace_2281960 : CollatzResearch.WordTrace tailWord_2281960 prefixEnd_2281960 43397863493851742766869 := by
  unfold tailWord_2281960
  simp only [CollatzResearch.WordTrace]
  refine ⟨41614959406428061292649667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55486612541904081723532889 41614959406428061292649667)
  ·
    refine ⟨62422439109642091938974501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41614959406428061292649667 62422439109642091938974501)
    ·
      refine ⟨11704207333057892238557719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62422439109642091938974501 11704207333057892238557719)
      ·
        refine ⟨17556310999586838357836579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11704207333057892238557719 17556310999586838357836579)
        ·
          refine ⟨26334466499380257536754869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17556310999586838357836579 26334466499380257536754869)
          ·
            refine ⟨2468856234316899144070769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26334466499380257536754869 2468856234316899144070769)
            ·
              refine ⟨1851642175737674358053077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2468856234316899144070769 1851642175737674358053077)
              ·
                refine ⟨43397863493851742766869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1851642175737674358053077 43397863493851742766869)
                ·
                  rfl

theorem cell23_2281960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 7].length) (baseStart_2281960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281960 prefixEnd_2281960 := by exact prefixLift 2281960
  have htrace : WordTrace (prefixWord ++ tailWord_2281960) baseStart_2281960 baseEnd_2281960 := by
    simpa [prefixWord, tailWord_2281960, baseEnd_2281960] using wordTrace_append hprefix tailTrace_2281960
  have hstable : (prefixWord ++ tailWord_2281960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281960).length < 2 ^ (prefixWord ++ tailWord_2281960).sum := by decide
  have hdescent : baseEnd_2281960 < baseStart_2281960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281980 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 5, 3, 2]
def baseStart_2281980 : Nat := 118140960795 + 2281980 * 2 ^ 59
def prefixEnd_2281980 : Nat := 4983230072969 + 3 ^ 40 * 2281980 * 2
def baseEnd_2281980 : Nat := 1171752583947086976455371

theorem tailTrace_2281980 : CollatzResearch.WordTrace tailWord_2281980 prefixEnd_2281980 1171752583947086976455371 := by
  unfold tailWord_2281980
  simp only [CollatzResearch.WordTrace]
  refine ⟨41615324136391833000513697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55487098848522444000684929 41615324136391833000513697)
  ·
    refine ⟨31211493102293874750385273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41615324136391833000513697 31211493102293874750385273)
    ·
      refine ⟨23408619826720406062788955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31211493102293874750385273 23408619826720406062788955)
      ·
        refine ⟨35112929740080609094183433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23408619826720406062788955 35112929740080609094183433)
        ·
          refine ⟨26334697305060456820637575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35112929740080609094183433 26334697305060456820637575)
          ·
            refine ⟨39502045957590685230956363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26334697305060456820637575 39502045957590685230956363)
            ·
              refine ⟨59253068936386027846434545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39502045957590685230956363 59253068936386027846434545)
              ·
                refine ⟨44439801702289520884825909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59253068936386027846434545 44439801702289520884825909)
                ·
                  refine ⟨4166231409589642582952429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44439801702289520884825909 4166231409589642582952429)
                  ·
                    refine ⟨1562336778596115968607161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4166231409589642582952429 1562336778596115968607161)
                    ·
                      refine ⟨1171752583947086976455371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1562336778596115968607161 1171752583947086976455371)
                      ·
                        rfl

theorem cell23_2281980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_2281980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281980 prefixEnd_2281980 := by exact prefixLift 2281980
  have htrace : WordTrace (prefixWord ++ tailWord_2281980) baseStart_2281980 baseEnd_2281980 := by
    simpa [prefixWord, tailWord_2281980, baseEnd_2281980] using wordTrace_append hprefix tailTrace_2281980
  have hstable : (prefixWord ++ tailWord_2281980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281980).length < 2 ^ (prefixWord ++ tailWord_2281980).sum := by decide
  have hdescent : baseEnd_2281980 < baseStart_2281980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281988 : List Nat := [2, 3, 2, 3, 1, 2, 3, 2, 1, 2, 2]
def baseStart_2281988 : Nat := 118140960795 + 2281988 * 2 ^ 59
def prefixEnd_2281988 : Nat := 4983230072969 + 3 ^ 40 * 2281988 * 2
def baseEnd_2281988 : Nat := 1171756691792322945155335

theorem tailTrace_2281988 : CollatzResearch.WordTrace tailWord_2281988 prefixEnd_2281988 1171756691792322945155335 := by
  unfold tailWord_2281988
  simp only [CollatzResearch.WordTrace]
  refine ⟨41615470028377341683659309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55487293371169788911545745 41615470028377341683659309)
  ·
    refine ⟨15605801260641503131372241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41615470028377341683659309 15605801260641503131372241)
    ·
      refine ⟨11704350945481127348529181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15605801260641503131372241 11704350945481127348529181)
      ·
        refine ⟨4389131604555422755698443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11704350945481127348529181 4389131604555422755698443)
        ·
          refine ⟨6583697406833134133547665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4389131604555422755698443 6583697406833134133547665)
          ·
            refine ⟨4937773055124850600160749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6583697406833134133547665 4937773055124850600160749)
            ·
              refine ⟨1851664895671818975060281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4937773055124850600160749 1851664895671818975060281)
              ·
                refine ⟨1388748671753864231295211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1851664895671818975060281 1388748671753864231295211)
                ·
                  refine ⟨2083123007630796346942817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1388748671753864231295211 2083123007630796346942817)
                  ·
                    refine ⟨1562342255723097260207113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2083123007630796346942817 1562342255723097260207113)
                    ·
                      refine ⟨1171756691792322945155335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1562342255723097260207113 1171756691792322945155335)
                      ·
                        rfl

theorem cell23_2281988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_2281988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281988 prefixEnd_2281988 := by exact prefixLift 2281988
  have htrace : WordTrace (prefixWord ++ tailWord_2281988) baseStart_2281988 baseEnd_2281988 := by
    simpa [prefixWord, tailWord_2281988, baseEnd_2281988] using wordTrace_append hprefix tailTrace_2281988
  have hstable : (prefixWord ++ tailWord_2281988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281988).length < 2 ^ (prefixWord ++ tailWord_2281988).sum := by decide
  have hdescent : baseEnd_2281988 < baseStart_2281988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282044 : List Nat := [2, 2, 2, 2, 3, 1, 1, 4, 2, 2, 2]
def baseStart_2282044 : Nat := 118140960795 + 2282044 * 2 ^ 59
def prefixEnd_2282044 : Nat := 4983230072969 + 3 ^ 40 * 2282044 * 2
def baseEnd_2282044 : Nat := 1171785446708974726055077

theorem tailTrace_2282044 : CollatzResearch.WordTrace tailWord_2282044 prefixEnd_2282044 1171785446708974726055077 := by
  unfold tailWord_2282044
  simp only [CollatzResearch.WordTrace]
  refine ⟨41616491272275902465678593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55488655029701203287571457 41616491272275902465678593)
  ·
    refine ⟨31212368454206926849258945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41616491272275902465678593 31212368454206926849258945)
    ·
      refine ⟨23409276340655195136944209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31212368454206926849258945 23409276340655195136944209)
      ·
        refine ⟨17556957255491396352708157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23409276340655195136944209 17556957255491396352708157)
        ·
          refine ⟨6583858970809273632265559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17556957255491396352708157 6583858970809273632265559)
          ·
            refine ⟨9875788456213910448398339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6583858970809273632265559 9875788456213910448398339)
            ·
              refine ⟨14813682684320865672597509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9875788456213910448398339 14813682684320865672597509)
              ·
                refine ⟨2777565503310162313612033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14813682684320865672597509 2777565503310162313612033)
                ·
                  refine ⟨2083174127482621735209025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2777565503310162313612033 2083174127482621735209025)
                  ·
                    refine ⟨1562380595611966301406769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2083174127482621735209025 1562380595611966301406769)
                    ·
                      refine ⟨1171785446708974726055077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1562380595611966301406769 1171785446708974726055077)
                      ·
                        rfl

theorem cell23_2282044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_2282044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282044 prefixEnd_2282044 := by exact prefixLift 2282044
  have htrace : WordTrace (prefixWord ++ tailWord_2282044) baseStart_2282044 baseEnd_2282044 := by
    simpa [prefixWord, tailWord_2282044, baseEnd_2282044] using wordTrace_append hprefix tailTrace_2282044
  have hstable : (prefixWord ++ tailWord_2282044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282044).length < 2 ^ (prefixWord ++ tailWord_2282044).sum := by decide
  have hdescent : baseEnd_2282044 < baseStart_2282044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282060 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 2, 3, 3]
def baseStart_2282060 : Nat := 118140960795 + 2282060 * 2 ^ 59
def prefixEnd_2282060 : Nat := 4983230072969 + 3 ^ 40 * 2282060 * 2
def baseEnd_2282060 : Nat := 1171793662399446663455003

theorem tailTrace_2282060 : CollatzResearch.WordTrace tailWord_2282060 prefixEnd_2282060 1171793662399446663455003 := by
  unfold tailWord_2282060
  simp only [CollatzResearch.WordTrace]
  refine ⟨41616783056246919831969817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55489044074995893109293089 41616783056246919831969817)
  ·
    refine ⟨31212587292185189873977363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41616783056246919831969817 31212587292185189873977363)
    ·
      refine ⟨46818880938277784810966045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31212587292185189873977363 46818880938277784810966045)
      ·
        refine ⟨17557080351854169304112267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46818880938277784810966045 17557080351854169304112267)
        ·
          refine ⟨26335620527781253956168401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17557080351854169304112267 26335620527781253956168401)
          ·
            refine ⟨19751715395835940467126301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26335620527781253956168401 19751715395835940467126301)
            ·
              refine ⟨7406893273438477675172363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19751715395835940467126301 7406893273438477675172363)
              ·
                refine ⟨11110339910157716512758545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7406893273438477675172363 11110339910157716512758545)
                ·
                  refine ⟨8332754932618287384568909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11110339910157716512758545 8332754932618287384568909)
                  ·
                    refine ⟨3124783099731857769213341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8332754932618287384568909 3124783099731857769213341)
                    ·
                      refine ⟨1171793662399446663455003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3124783099731857769213341 1171793662399446663455003)
                      ·
                        rfl

theorem cell23_2282060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_2282060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282060 prefixEnd_2282060 := by exact prefixLift 2282060
  have htrace : WordTrace (prefixWord ++ tailWord_2282060) baseStart_2282060 baseEnd_2282060 := by
    simpa [prefixWord, tailWord_2282060, baseEnd_2282060] using wordTrace_append hprefix tailTrace_2282060
  have hstable : (prefixWord ++ tailWord_2282060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282060).length < 2 ^ (prefixWord ++ tailWord_2282060).sum := by decide
  have hdescent : baseEnd_2282060 < baseStart_2282060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282061 : List Nat := [1, 6, 1, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_2282061 : Nat := 118140960795 + 2282061 * 2 ^ 59
def prefixEnd_2282061 : Nat := 4983230072969 + 3 ^ 40 * 2282061 * 2
def baseEnd_2282061 : Nat := 1171794175880101159542499

theorem tailTrace_2282061 : CollatzResearch.WordTrace tailWord_2282061 prefixEnd_2282061 1171794175880101159542499 := by
  unfold tailWord_2282061
  simp only [CollatzResearch.WordTrace]
  refine ⟨83233602585490216834726037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55489068390326811223150691 83233602585490216834726037)
  ·
    refine ⟨3901575121194853914127783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 83233602585490216834726037 3901575121194853914127783)
    ·
      refine ⟨5852362681792280871191675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3901575121194853914127783 5852362681792280871191675)
      ·
        refine ⟨8778544022688421306787513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5852362681792280871191675 8778544022688421306787513)
        ·
          refine ⟨6583908017016315980090635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8778544022688421306787513 6583908017016315980090635)
          ·
            refine ⟨9875862025524473970135953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6583908017016315980090635 9875862025524473970135953)
            ·
              refine ⟨7406896519143355477601965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9875862025524473970135953 7406896519143355477601965)
              ·
                refine ⟨2777586194678758304100737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7406896519143355477601965 2777586194678758304100737)
                ·
                  refine ⟨2083189646009068728075553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2777586194678758304100737 2083189646009068728075553)
                  ·
                    refine ⟨1562392234506801546056665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2083189646009068728075553 1562392234506801546056665)
                    ·
                      refine ⟨1171794175880101159542499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1562392234506801546056665 1171794175880101159542499)
                      ·
                        rfl

theorem cell23_2282061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_2282061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282061 prefixEnd_2282061 := by exact prefixLift 2282061
  have htrace : WordTrace (prefixWord ++ tailWord_2282061) baseStart_2282061 baseEnd_2282061 := by
    simpa [prefixWord, tailWord_2282061, baseEnd_2282061] using wordTrace_append hprefix tailTrace_2282061
  have hstable : (prefixWord ++ tailWord_2282061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282061).length < 2 ^ (prefixWord ++ tailWord_2282061).sum := by decide
  have hdescent : baseEnd_2282061 < baseStart_2282061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282063 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 4, 5]
def baseStart_2282063 : Nat := 118140960795 + 2282063 * 2 ^ 59
def prefixEnd_2282063 : Nat := 4983230072969 + 3 ^ 40 * 2282063 * 2
def baseEnd_2282063 : Nat := 390598400947136717239163

theorem tailTrace_2282063 : CollatzResearch.WordTrace tailWord_2282063 prefixEnd_2282063 390598400947136717239163 := by
  unfold tailWord_2282063
  simp only [CollatzResearch.WordTrace]
  refine ⟨83233675531482971176298843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55489117020988647450865895 83233675531482971176298843)
  ·
    refine ⟨124850513297224456764448265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83233675531482971176298843 124850513297224456764448265)
    ·
      refine ⟨93637884972918342573336199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124850513297224456764448265 93637884972918342573336199)
      ·
        refine ⟨140456827459377513860004299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93637884972918342573336199 140456827459377513860004299)
        ·
          refine ⟨210685241189066270790006449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140456827459377513860004299 210685241189066270790006449)
          ·
            refine ⟨158013930891799703092504837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210685241189066270790006449 158013930891799703092504837)
            ·
              refine ⟨29627612042212444329844657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 158013930891799703092504837 29627612042212444329844657)
              ·
                refine ⟨22220709031659333247383493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29627612042212444329844657 22220709031659333247383493)
                ·
                  refine ⟨4166382943436124983884405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22220709031659333247383493 4166382943436124983884405)
                  ·
                    refine ⟨390598400947136717239163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4166382943436124983884405 390598400947136717239163)
                    ·
                      rfl

theorem cell23_2282063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 5].length) (baseStart_2282063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282063 prefixEnd_2282063 := by exact prefixLift 2282063
  have htrace : WordTrace (prefixWord ++ tailWord_2282063) baseStart_2282063 baseEnd_2282063 := by
    simpa [prefixWord, tailWord_2282063, baseEnd_2282063] using wordTrace_append hprefix tailTrace_2282063
  have hstable : (prefixWord ++ tailWord_2282063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282063).length < 2 ^ (prefixWord ++ tailWord_2282063).sum := by decide
  have hdescent : baseEnd_2282063 < baseStart_2282063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282080 : List Nat := [2, 1, 1, 3, 2, 1, 5, 1, 2, 5]
def baseStart_2282080 : Nat := 118140960795 + 2282080 * 2 ^ 59
def prefixEnd_2282080 : Nat := 4983230072969 + 3 ^ 40 * 2282080 * 2
def baseEnd_2282080 : Nat := 390601310670845528401637

theorem tailTrace_2282080 : CollatzResearch.WordTrace tailWord_2282080 prefixEnd_2282080 390601310670845528401637 := by
  unfold tailWord_2282080
  simp only [CollatzResearch.WordTrace]
  refine ⟨41617147786210691539833847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55489530381614255386445129 41617147786210691539833847)
  ·
    refine ⟨62425721679316037309750771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41617147786210691539833847 62425721679316037309750771)
    ·
      refine ⟨93638582518974055964626157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62425721679316037309750771 93638582518974055964626157)
      ·
        refine ⟨35114468444615270986734809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93638582518974055964626157 35114468444615270986734809)
        ·
          refine ⟨26335851333461453240051107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35114468444615270986734809 26335851333461453240051107)
          ·
            refine ⟨39503777000192179860076661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26335851333461453240051107 39503777000192179860076661)
            ·
              refine ⟨3703479093768016861882187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39503777000192179860076661 3703479093768016861882187)
              ·
                refine ⟨5555218640652025292823281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3703479093768016861882187 5555218640652025292823281)
                ·
                  refine ⟨4166413980489018969617461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5555218640652025292823281 4166413980489018969617461)
                  ·
                    refine ⟨390601310670845528401637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4166413980489018969617461 390601310670845528401637)
                    ·
                      rfl

theorem cell23_2282080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 2, 5].length) (baseStart_2282080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282080 prefixEnd_2282080 := by exact prefixLift 2282080
  have htrace : WordTrace (prefixWord ++ tailWord_2282080) baseStart_2282080 baseEnd_2282080 := by
    simpa [prefixWord, tailWord_2282080, baseEnd_2282080] using wordTrace_append hprefix tailTrace_2282080
  have hstable : (prefixWord ++ tailWord_2282080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282080).length < 2 ^ (prefixWord ++ tailWord_2282080).sum := by decide
  have hdescent : baseEnd_2282080 < baseStart_2282080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282103 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 5]
def baseStart_2282103 : Nat := 118140960795 + 2282103 * 2 ^ 59
def prefixEnd_2282103 : Nat := 4983230072969 + 3 ^ 40 * 2282103 * 2
def baseEnd_2282103 : Nat := 1171815742067589995217305

theorem tailTrace_2282103 : CollatzResearch.WordTrace tailWord_2282103 prefixEnd_2282103 1171815742067589995217305 := by
  unfold tailWord_2282103
  simp only [CollatzResearch.WordTrace]
  refine ⟨83235134451338058007754963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55490089634225372005169975 83235134451338058007754963)
  ·
    refine ⟨124852701677007087011632445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83235134451338058007754963 124852701677007087011632445)
    ·
      refine ⟨46819763128877657629362167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124852701677007087011632445 46819763128877657629362167)
      ·
        refine ⟨70229644693316486444043251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46819763128877657629362167 70229644693316486444043251)
        ·
          refine ⟨105344467039974729666064877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70229644693316486444043251 105344467039974729666064877)
          ·
            refine ⟨39504175139990523624774329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105344467039974729666064877 39504175139990523624774329)
            ·
              refine ⟨29628131354992892718580747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39504175139990523624774329 29628131354992892718580747)
              ·
                refine ⟨44442197032489339077871121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29628131354992892718580747 44442197032489339077871121)
                ·
                  refine ⟨33331647774367004308403341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44442197032489339077871121 33331647774367004308403341)
                  ·
                    refine ⟨12499367915387626615651253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33331647774367004308403341 12499367915387626615651253)
                    ·
                      refine ⟨1171815742067589995217305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12499367915387626615651253 1171815742067589995217305)
                      ·
                        rfl

theorem cell23_2282103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_2282103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282103 prefixEnd_2282103 := by exact prefixLift 2282103
  have htrace : WordTrace (prefixWord ++ tailWord_2282103) baseStart_2282103 baseEnd_2282103 := by
    simpa [prefixWord, tailWord_2282103, baseEnd_2282103] using wordTrace_append hprefix tailTrace_2282103
  have hstable : (prefixWord ++ tailWord_2282103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282103).length < 2 ^ (prefixWord ++ tailWord_2282103).sum := by decide
  have hdescent : baseEnd_2282103 < baseStart_2282103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282117 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 2, 4, 2]
def baseStart_2282117 : Nat := 118140960795 + 2282117 * 2 ^ 59
def prefixEnd_2282117 : Nat := 4983230072969 + 3 ^ 40 * 2282117 * 2
def baseEnd_2282117 : Nat := 1171822930796752940442241

theorem tailTrace_2282117 : CollatzResearch.WordTrace tailWord_2282117 prefixEnd_2282117 1171822930796752940442241 := by
  unfold tailWord_2282117
  simp only [CollatzResearch.WordTrace]
  refine ⟨83235645073287338398764605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55490430048858225599176403 83235645073287338398764605)
  ·
    refine ⟨31213366902482751899536727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83235645073287338398764605 31213366902482751899536727)
    ·
      refine ⟨46820050353724127849305091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31213366902482751899536727 46820050353724127849305091)
      ·
        refine ⟨70230075530586191773957637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46820050353724127849305091 70230075530586191773957637)
        ·
          refine ⟨13168139161984910957617057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70230075530586191773957637 13168139161984910957617057)
          ·
            refine ⟨9876104371488683218212793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13168139161984910957617057 9876104371488683218212793)
            ·
              refine ⟨7407078278616512413659595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9876104371488683218212793 7407078278616512413659595)
              ·
                refine ⟨11110617417924768620489393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7407078278616512413659595 11110617417924768620489393)
                ·
                  refine ⟨8332963063443576465367045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11110617417924768620489393 8332963063443576465367045)
                  ·
                    refine ⟨1562430574395670587256321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8332963063443576465367045 1562430574395670587256321)
                    ·
                      refine ⟨1171822930796752940442241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1562430574395670587256321 1171822930796752940442241)
                      ·
                        rfl

theorem cell23_2282117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 4, 2].length) (baseStart_2282117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282117 prefixEnd_2282117 := by exact prefixLift 2282117
  have htrace : WordTrace (prefixWord ++ tailWord_2282117) baseStart_2282117 baseEnd_2282117 := by
    simpa [prefixWord, tailWord_2282117, baseEnd_2282117] using wordTrace_append hprefix tailTrace_2282117
  have hstable : (prefixWord ++ tailWord_2282117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282117).length < 2 ^ (prefixWord ++ tailWord_2282117).sum := by decide
  have hdescent : baseEnd_2282117 < baseStart_2282117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282133 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_2282133 : Nat := 118140960795 + 2282133 * 2 ^ 59
def prefixEnd_2282133 : Nat := 4983230072969 + 3 ^ 40 * 2282133 * 2
def baseEnd_2282133 : Nat := 1171831146487224877842167

theorem tailTrace_2282133 : CollatzResearch.WordTrace tailWord_2282133 prefixEnd_2282133 1171831146487224877842167 := by
  unfold tailWord_2282133
  simp only [CollatzResearch.WordTrace]
  refine ⟨83236228641229373131347053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55490819094152915420898035 83236228641229373131347053)
  ·
    refine ⟨31213585740461014924255145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83236228641229373131347053 31213585740461014924255145)
    ·
      refine ⟨23410189305345761193191359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31213585740461014924255145 23410189305345761193191359)
      ·
        refine ⟨35115283958018641789787039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23410189305345761193191359 35115283958018641789787039)
        ·
          refine ⟨52672925937027962684680559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35115283958018641789787039 52672925937027962684680559)
          ·
            refine ⟨79009388905541944027020839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52672925937027962684680559 79009388905541944027020839)
            ·
              refine ⟨118514083358312916040531259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79009388905541944027020839 118514083358312916040531259)
              ·
                refine ⟨177771125037469374060796889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118514083358312916040531259 177771125037469374060796889)
                ·
                  refine ⟨133328343778102030545597667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177771125037469374060796889 133328343778102030545597667)
                  ·
                    refine ⟨199992515667153045818396501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 133328343778102030545597667 199992515667153045818396501)
                    ·
                      refine ⟨1171831146487224877842167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 199992515667153045818396501 1171831146487224877842167)
                      ·
                        rfl

theorem cell23_2282133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_2282133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282133 prefixEnd_2282133 := by exact prefixLift 2282133
  have htrace : WordTrace (prefixWord ++ tailWord_2282133) baseStart_2282133 baseEnd_2282133 := by
    simpa [prefixWord, tailWord_2282133, baseEnd_2282133] using wordTrace_append hprefix tailTrace_2282133
  have hstable : (prefixWord ++ tailWord_2282133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282133).length < 2 ^ (prefixWord ++ tailWord_2282133).sum := by decide
  have hdescent : baseEnd_2282133 < baseStart_2282133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282140 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 8]
def baseStart_2282140 : Nat := 118140960795 + 2282140 * 2 ^ 59
def prefixEnd_2282140 : Nat := 4983230072969 + 3 ^ 40 * 2282140 * 2
def baseEnd_2282140 : Nat := 130203860094645150050515

theorem tailTrace_2282140 : CollatzResearch.WordTrace tailWord_2282140 prefixEnd_2282140 130203860094645150050515 := by
  unfold tailWord_2282140
  simp only [CollatzResearch.WordTrace]
  refine ⟨41618241976102006663425937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55490989301469342217901249 41618241976102006663425937)
  ·
    refine ⟨31213681482076504997569453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41618241976102006663425937 31213681482076504997569453)
    ·
      refine ⟨11705130555778689374088545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31213681482076504997569453 11705130555778689374088545)
      ·
        refine ⟨8778847916834017030566409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11705130555778689374088545 8778847916834017030566409)
        ·
          refine ⟨6584135937625512772924807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8778847916834017030566409 6584135937625512772924807)
          ·
            refine ⟨9876203906438269159387211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6584135937625512772924807 9876203906438269159387211)
            ·
              refine ⟨14814305859657403739080817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9876203906438269159387211 14814305859657403739080817)
              ·
                refine ⟨11110729394743052804310613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14814305859657403739080817 11110729394743052804310613)
                ·
                  refine ⟨130203860094645150050515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11110729394743052804310613 130203860094645150050515)
                  ·
                    rfl

theorem cell23_2282140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 8].length) (baseStart_2282140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282140 prefixEnd_2282140 := by exact prefixLift 2282140
  have htrace : WordTrace (prefixWord ++ tailWord_2282140) baseStart_2282140 baseEnd_2282140 := by
    simpa [prefixWord, tailWord_2282140, baseEnd_2282140] using wordTrace_append hprefix tailTrace_2282140
  have hstable : (prefixWord ++ tailWord_2282140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282140).length < 2 ^ (prefixWord ++ tailWord_2282140).sum := by decide
  have hdescent : baseEnd_2282140 < baseStart_2282140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282161 : List Nat := [1, 2, 2, 6, 1, 2, 1, 1, 3, 4]
def baseStart_2282161 : Nat := 118140960795 + 2282161 * 2 ^ 59
def prefixEnd_2282161 : Nat := 4983230072969 + 3 ^ 40 * 2282161 * 2
def baseEnd_2282161 : Nat := 390615174648516922764013

theorem tailTrace_2282161 : CollatzResearch.WordTrace tailWord_2282161 prefixEnd_2282161 390615174648516922764013 := by
  unfold tailWord_2282161
  simp only [CollatzResearch.WordTrace]
  refine ⟨83237249885127933913366337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55491499923418622608910891 83237249885127933913366337)
  ·
    refine ⟨62427937413845950435024753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83237249885127933913366337 62427937413845950435024753)
    ·
      refine ⟨46820953060384462826268565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62427937413845950435024753 46820953060384462826268565)
      ·
        refine ⟨2194732174705521694981339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46820953060384462826268565 2194732174705521694981339)
        ·
          refine ⟨3292098262058282542472009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2194732174705521694981339 3292098262058282542472009)
          ·
            refine ⟨2469073696543711906854007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3292098262058282542472009 2469073696543711906854007)
            ·
              refine ⟨3703610544815567860281011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469073696543711906854007 3703610544815567860281011)
              ·
                refine ⟨5555415817223351790421517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3703610544815567860281011 5555415817223351790421517)
                ·
                  refine ⟨2083280931458756921408069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5555415817223351790421517 2083280931458756921408069)
                  ·
                    refine ⟨390615174648516922764013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2083280931458756921408069 390615174648516922764013)
                    ·
                      rfl

theorem cell23_2282161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_2282161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282161 prefixEnd_2282161 := by exact prefixLift 2282161
  have htrace : WordTrace (prefixWord ++ tailWord_2282161) baseStart_2282161 baseEnd_2282161 := by
    simpa [prefixWord, tailWord_2282161, baseEnd_2282161] using wordTrace_append hprefix tailTrace_2282161
  have hstable : (prefixWord ++ tailWord_2282161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282161).length < 2 ^ (prefixWord ++ tailWord_2282161).sum := by decide
  have hdescent : baseEnd_2282161 < baseStart_2282161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282170 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 3, 5]
def baseStart_2282170 : Nat := 118140960795 + 2282170 * 2 ^ 59
def prefixEnd_2282170 : Nat := 4983230072969 + 3 ^ 40 * 2282170 * 2
def baseEnd_2282170 : Nat := 390616715090480411026499

theorem tailTrace_2282170 : CollatzResearch.WordTrace tailWord_2282170 prefixEnd_2282170 390616715090480411026499 := by
  unfold tailWord_2282170
  simp only [CollatzResearch.WordTrace]
  refine ⟨20809394535523832112610991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55491718761396885633629309 20809394535523832112610991)
  ·
    refine ⟨31214091803285748168916487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20809394535523832112610991 31214091803285748168916487)
    ·
      refine ⟨46821137704928622253374731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31214091803285748168916487 46821137704928622253374731)
      ·
        refine ⟨70231706557392933380062097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46821137704928622253374731 70231706557392933380062097)
        ·
          refine ⟨52673779918044700035046573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70231706557392933380062097 52673779918044700035046573)
          ·
            refine ⟨19752667469266762513142465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52673779918044700035046573 19752667469266762513142465)
            ·
              refine ⟨14814500601950071884856849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19752667469266762513142465 14814500601950071884856849)
              ·
                refine ⟨11110875451462553913642637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14814500601950071884856849 11110875451462553913642637)
                ·
                  refine ⟨4166578294298457717615989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11110875451462553913642637 4166578294298457717615989)
                  ·
                    refine ⟨390616715090480411026499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4166578294298457717615989 390616715090480411026499)
                    ·
                      rfl

theorem cell23_2282170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_2282170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282170 prefixEnd_2282170 := by exact prefixLift 2282170
  have htrace : WordTrace (prefixWord ++ tailWord_2282170) baseStart_2282170 baseEnd_2282170 := by
    simpa [prefixWord, tailWord_2282170, baseEnd_2282170] using wordTrace_append hprefix tailTrace_2282170
  have hstable : (prefixWord ++ tailWord_2282170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282170).length < 2 ^ (prefixWord ++ tailWord_2282170).sum := by decide
  have hdescent : baseEnd_2282170 < baseStart_2282170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282200 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 3, 6]
def baseStart_2282200 : Nat := 118140960795 + 2282200 * 2 ^ 59
def prefixEnd_2282200 : Nat := 4983230072969 + 3 ^ 40 * 2282200 * 2
def baseEnd_2282200 : Nat := 390621849897025371901453

theorem tailTrace_2282200 : CollatzResearch.WordTrace tailWord_2282200 prefixEnd_2282200 390621849897025371901453 := by
  unfold tailWord_2282200
  simp only [CollatzResearch.WordTrace]
  refine ⟨41619336165993321787018027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55492448221324429049357369 41619336165993321787018027)
  ·
    refine ⟨62429004248989982680527041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41619336165993321787018027 62429004248989982680527041)
    ·
      refine ⟨46821753186742487010395281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62429004248989982680527041 46821753186742487010395281)
      ·
        refine ⟨35116314890056865257796461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46821753186742487010395281 35116314890056865257796461)
        ·
          refine ⟨13168618083771324471673673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35116314890056865257796461 13168618083771324471673673)
          ·
            refine ⟨9876463562828493353755255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13168618083771324471673673 9876463562828493353755255)
            ·
              refine ⟨14814695344242740030632883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9876463562828493353755255 14814695344242740030632883)
              ·
                refine ⟨22222043016364110045949325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14814695344242740030632883 22222043016364110045949325)
                ·
                  refine ⟨8333266131136541267230997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22222043016364110045949325 8333266131136541267230997)
                  ·
                    refine ⟨390621849897025371901453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8333266131136541267230997 390621849897025371901453)
                    ·
                      rfl

theorem cell23_2282200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_2282200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282200 prefixEnd_2282200 := by exact prefixLift 2282200
  have htrace : WordTrace (prefixWord ++ tailWord_2282200) baseStart_2282200 baseEnd_2282200 := by
    simpa [prefixWord, tailWord_2282200, baseEnd_2282200] using wordTrace_append hprefix tailTrace_2282200
  have hstable : (prefixWord ++ tailWord_2282200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282200).length < 2 ^ (prefixWord ++ tailWord_2282200).sum := by decide
  have hdescent : baseEnd_2282200 < baseStart_2282200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282217 : List Nat := [1, 2, 1, 1, 1, 2, 5, 4, 2, 4]
def baseStart_2282217 : Nat := 118140960795 + 2282217 * 2 ^ 59
def prefixEnd_2282217 : Nat := 4983230072969 + 3 ^ 40 * 2282217 * 2
def baseEnd_2282217 : Nat := 390624759620734183063927

theorem tailTrace_2282217 : CollatzResearch.WordTrace tailWord_2282217 prefixEnd_2282217 390624759620734183063927 := by
  unfold tailWord_2282217
  simp only [CollatzResearch.WordTrace]
  refine ⟨83239292372925055477404905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55492861581950036984936603 83239292372925055477404905)
  ·
    refine ⟨62429469279693791608053679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83239292372925055477404905 62429469279693791608053679)
    ·
      refine ⟨93644203919540687412080519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62429469279693791608053679 93644203919540687412080519)
      ·
        refine ⟨140466305879311031118120779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93644203919540687412080519 140466305879311031118120779)
        ·
          refine ⟨210699458818966546677181169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140466305879311031118120779 210699458818966546677181169)
          ·
            refine ⟨158024594114224910007885877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210699458818966546677181169 158024594114224910007885877)
            ·
              refine ⟨14814805698208585313239301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 158024594114224910007885877 14814805698208585313239301)
              ·
                refine ⟨2777776068414109746232369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14814805698208585313239301 2777776068414109746232369)
                ·
                  refine ⟨2083332051310582309674277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2777776068414109746232369 2083332051310582309674277)
                  ·
                    refine ⟨390624759620734183063927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2083332051310582309674277 390624759620734183063927)
                    ·
                      rfl

theorem cell23_2282217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 4].length) (baseStart_2282217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282217 prefixEnd_2282217 := by exact prefixLift 2282217
  have htrace : WordTrace (prefixWord ++ tailWord_2282217) baseStart_2282217 baseEnd_2282217 := by
    simpa [prefixWord, tailWord_2282217, baseEnd_2282217] using wordTrace_append hprefix tailTrace_2282217
  have hstable : (prefixWord ++ tailWord_2282217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282217).length < 2 ^ (prefixWord ++ tailWord_2282217).sum := by decide
  have hdescent : baseEnd_2282217 < baseStart_2282217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282220 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 4]
def baseStart_2282220 : Nat := 118140960795 + 2282220 * 2 ^ 59
def prefixEnd_2282220 : Nat := 4983230072969 + 3 ^ 40 * 2282220 * 2
def baseEnd_2282220 : Nat := 1171875819304166037454267

theorem tailTrace_2282220 : CollatzResearch.WordTrace tailWord_2282220 prefixEnd_2282220 1171875819304166037454267 := by
  unfold tailWord_2282220
  simp only [CollatzResearch.WordTrace]
  refine ⟨41619700895957093494882057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55492934527942791326509409 41619700895957093494882057)
  ·
    refine ⟨31214775671967820121161543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41619700895957093494882057 31214775671967820121161543)
    ·
      refine ⟨46822163507951730181742315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31214775671967820121161543 46822163507951730181742315)
      ·
        refine ⟨70233245261927595272613473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46822163507951730181742315 70233245261927595272613473)
        ·
          refine ⟨52674933946445696454460105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70233245261927595272613473 52674933946445696454460105)
          ·
            refine ⟨39506200459834272340845079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52674933946445696454460105 39506200459834272340845079)
            ·
              refine ⟨59259300689751408511267619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39506200459834272340845079 59259300689751408511267619)
              ·
                refine ⟨88888951034627112766901429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59259300689751408511267619 88888951034627112766901429)
                ·
                  refine ⟨8333339159496291821897009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88888951034627112766901429 8333339159496291821897009)
                  ·
                    refine ⟨6250004369622218866422757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8333339159496291821897009 6250004369622218866422757)
                    ·
                      refine ⟨1171875819304166037454267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6250004369622218866422757 1171875819304166037454267)
                      ·
                        rfl

theorem cell23_2282220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_2282220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282220 prefixEnd_2282220 := by exact prefixLift 2282220
  have htrace : WordTrace (prefixWord ++ tailWord_2282220) baseStart_2282220 baseEnd_2282220 := by
    simpa [prefixWord, tailWord_2282220, baseEnd_2282220] using wordTrace_append hprefix tailTrace_2282220
  have hstable : (prefixWord ++ tailWord_2282220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282220).length < 2 ^ (prefixWord ++ tailWord_2282220).sum := by decide
  have hdescent : baseEnd_2282220 < baseStart_2282220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282224 : List Nat := [2, 1, 1, 1, 3, 1, 4, 3, 3, 2, 2]
def baseStart_2282224 : Nat := 118140960795 + 2282224 * 2 ^ 59
def prefixEnd_2282224 : Nat := 4983230072969 + 3 ^ 40 * 2282224 * 2
def baseEnd_2282224 : Nat := 1171877873226784021804249

theorem tailTrace_2282224 : CollatzResearch.WordTrace tailWord_2282224 prefixEnd_2282224 1171877873226784021804249 := by
  unfold tailWord_2282224
  simp only [CollatzResearch.WordTrace]
  refine ⟨41619773841949847836454863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55493031789266463781939817 41619773841949847836454863)
  ·
    refine ⟨62429660762924771754682295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41619773841949847836454863 62429660762924771754682295)
    ·
      refine ⟨93644491144387157632023443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62429660762924771754682295 93644491144387157632023443)
      ·
        refine ⟨140466736716580736448035165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93644491144387157632023443 140466736716580736448035165)
        ·
          refine ⟨52675026268717776168013187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140466736716580736448035165 52675026268717776168013187)
          ·
            refine ⟨79012539403076664252019781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52675026268717776168013187 79012539403076664252019781)
            ·
              refine ⟨14814851138076874547253709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79012539403076664252019781 14814851138076874547253709)
              ·
                refine ⟨5555569176778827955220141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14814851138076874547253709 5555569176778827955220141)
                ·
                  refine ⟨2083338441292060483207553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5555569176778827955220141 2083338441292060483207553)
                  ·
                    refine ⟨1562503830969045362405665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2083338441292060483207553 1562503830969045362405665)
                    ·
                      refine ⟨1171877873226784021804249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1562503830969045362405665 1171877873226784021804249)
                      ·
                        rfl

theorem cell23_2282224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 3, 2, 2].length) (baseStart_2282224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282224 prefixEnd_2282224 := by exact prefixLift 2282224
  have htrace : WordTrace (prefixWord ++ tailWord_2282224) baseStart_2282224 baseEnd_2282224 := by
    simpa [prefixWord, tailWord_2282224, baseEnd_2282224] using wordTrace_append hprefix tailTrace_2282224
  have hstable : (prefixWord ++ tailWord_2282224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282224).length < 2 ^ (prefixWord ++ tailWord_2282224).sum := by decide
  have hdescent : baseEnd_2282224 < baseStart_2282224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282237 : List Nat := [1, 4, 1, 1, 1, 1, 6, 1, 1, 2, 4]
def baseStart_2282237 : Nat := 118140960795 + 2282237 * 2 ^ 59
def prefixEnd_2282237 : Nat := 4983230072969 + 3 ^ 40 * 2282237 * 2
def baseEnd_2282237 : Nat := 1171884548475292470941689

theorem tailTrace_2282237 : CollatzResearch.WordTrace tailWord_2282237 prefixEnd_2282237 1171884548475292470941689 := by
  unfold tailWord_2282237
  simp only [CollatzResearch.WordTrace]
  refine ⟨83240021832852598893132965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55493347888568399262088643 83240021832852598893132965)
  ·
    refine ⟨15607504093659862292462431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83240021832852598893132965 15607504093659862292462431)
    ·
      refine ⟨23411256140489793438693647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15607504093659862292462431 23411256140489793438693647)
      ·
        refine ⟨35116884210734690158040471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23411256140489793438693647 35116884210734690158040471)
        ·
          refine ⟨52675326316102035237060707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35116884210734690158040471 52675326316102035237060707)
          ·
            refine ⟨79012989474153052855591061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52675326316102035237060707 79012989474153052855591061)
            ·
              refine ⟨3703733881600924352605831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79012989474153052855591061 3703733881600924352605831)
              ·
                refine ⟨5555600822401386528908747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3703733881600924352605831 5555600822401386528908747)
                ·
                  refine ⟨8333401233602079793363121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5555600822401386528908747 8333401233602079793363121)
                  ·
                    refine ⟨6250050925201559845022341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8333401233602079793363121 6250050925201559845022341)
                    ·
                      refine ⟨1171884548475292470941689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6250050925201559845022341 1171884548475292470941689)
                      ·
                        rfl

theorem cell23_2282237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_2282237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282237 prefixEnd_2282237 := by exact prefixLift 2282237
  have htrace : WordTrace (prefixWord ++ tailWord_2282237) baseStart_2282237 baseEnd_2282237 := by
    simpa [prefixWord, tailWord_2282237, baseEnd_2282237] using wordTrace_append hprefix tailTrace_2282237
  have hstable : (prefixWord ++ tailWord_2282237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282237).length < 2 ^ (prefixWord ++ tailWord_2282237).sum := by decide
  have hdescent : baseEnd_2282237 < baseStart_2282237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282244 : List Nat := [2, 3, 2, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_2282244 : Nat := 118140960795 + 2282244 * 2 ^ 59
def prefixEnd_2282244 : Nat := 4983230072969 + 3 ^ 40 * 2282244 * 2
def baseEnd_2282244 : Nat := 1171888142839873943554157

theorem tailTrace_2282244 : CollatzResearch.WordTrace tailWord_2282244 prefixEnd_2282244 1171888142839873943554157 := by
  unfold tailWord_2282244
  simp only [CollatzResearch.WordTrace]
  refine ⟨41620138571913619544318893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55493518095884826059091857 41620138571913619544318893)
  ·
    refine ⟨15607551964467607329119585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41620138571913619544318893 15607551964467607329119585)
    ·
      refine ⟨11705663973350705496839689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15607551964467607329119585 11705663973350705496839689)
      ·
        refine ⟨8779247980013029122629767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11705663973350705496839689 8779247980013029122629767)
        ·
          refine ⟨13168871970019543683944651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8779247980013029122629767 13168871970019543683944651)
          ·
            refine ⟨19753307955029315525916977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13168871970019543683944651 19753307955029315525916977)
            ·
              refine ⟨14814980966271986644437733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19753307955029315525916977 14814980966271986644437733)
              ·
                refine ⟨2777808931175997495832075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14814980966271986644437733 2777808931175997495832075)
                ·
                  refine ⟨4166713396763996243748113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2777808931175997495832075 4166713396763996243748113)
                  ·
                    refine ⟨3125035047572997182811085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4166713396763996243748113 3125035047572997182811085)
                    ·
                      refine ⟨1171888142839873943554157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3125035047572997182811085 1171888142839873943554157)
                      ·
                        rfl

theorem cell23_2282244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_2282244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282244 prefixEnd_2282244 := by exact prefixLift 2282244
  have htrace : WordTrace (prefixWord ++ tailWord_2282244) baseStart_2282244 baseEnd_2282244 := by
    simpa [prefixWord, tailWord_2282244, baseEnd_2282244] using wordTrace_append hprefix tailTrace_2282244
  have hstable : (prefixWord ++ tailWord_2282244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282244).length < 2 ^ (prefixWord ++ tailWord_2282244).sum := by decide
  have hdescent : baseEnd_2282244 < baseStart_2282244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282257 : List Nat := [1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 3]
def baseStart_2282257 : Nat := 118140960795 + 2282257 * 2 ^ 59
def prefixEnd_2282257 : Nat := 4983230072969 + 3 ^ 40 * 2282257 * 2
def baseEnd_2282257 : Nat := 1171894818088382392691597

theorem tailTrace_2282257 : CollatzResearch.WordTrace tailWord_2282257 prefixEnd_2282257 1171894818088382392691597 := by
  unfold tailWord_2282257
  simp only [CollatzResearch.WordTrace]
  refine ⟨83240751292780142308861025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55493834195186761539240683 83240751292780142308861025)
  ·
    refine ⟨62430563469585106731645769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83240751292780142308861025 62430563469585106731645769)
    ·
      refine ⟨46822922602188830048734327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62430563469585106731645769 46822922602188830048734327)
      ·
        refine ⟨70234383903283245073101491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46822922602188830048734327 70234383903283245073101491)
        ·
          refine ⟨105351575854924867609652237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70234383903283245073101491 105351575854924867609652237)
          ·
            refine ⟨39506840945596825353619589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105351575854924867609652237 39506840945596825353619589)
            ·
              refine ⟨7407532677299404753803673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39506840945596825353619589 7407532677299404753803673)
              ·
                refine ⟨5555649507974553565352755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7407532677299404753803673 5555649507974553565352755)
                ·
                  refine ⟨8333474261961830348029133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5555649507974553565352755 8333474261961830348029133)
                  ·
                    refine ⟨3125052848235686380510925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8333474261961830348029133 3125052848235686380510925)
                    ·
                      refine ⟨1171894818088382392691597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3125052848235686380510925 1171894818088382392691597)
                      ·
                        rfl

theorem cell23_2282257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_2282257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282257 prefixEnd_2282257 := by exact prefixLift 2282257
  have htrace : WordTrace (prefixWord ++ tailWord_2282257) baseStart_2282257 baseEnd_2282257 := by
    simpa [prefixWord, tailWord_2282257, baseEnd_2282257] using wordTrace_append hprefix tailTrace_2282257
  have hstable : (prefixWord ++ tailWord_2282257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282257).length < 2 ^ (prefixWord ++ tailWord_2282257).sum := by decide
  have hdescent : baseEnd_2282257 < baseStart_2282257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282285 : List Nat := [1, 5, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_2282285 : Nat := 118140960795 + 2282285 * 2 ^ 59
def prefixEnd_2282285 : Nat := 4983230072969 + 3 ^ 40 * 2282285 * 2
def baseEnd_2282285 : Nat := 390636398515569427713823

theorem tailTrace_2282285 : CollatzResearch.WordTrace tailWord_2282285 prefixEnd_2282285 390636398515569427713823 := by
  unfold tailWord_2282285
  simp only [CollatzResearch.WordTrace]
  refine ⟨83241772536678703090880309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55494515024452468727253539 83241772536678703090880309)
  ·
    refine ⟨7803916175313628414770029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83241772536678703090880309 7803916175313628414770029)
    ·
      refine ⟨2926468565742610655538761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7803916175313628414770029 2926468565742610655538761)
      ·
        refine ⟨2194851424306957991654071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2926468565742610655538761 2194851424306957991654071)
        ·
          refine ⟨3292277136460436987481107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2194851424306957991654071 3292277136460436987481107)
          ·
            refine ⟨4938415704690655481221661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3292277136460436987481107 4938415704690655481221661)
            ·
              refine ⟨1851905889258995805458123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4938415704690655481221661 1851905889258995805458123)
              ·
                refine ⟨2777858833888493708187185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1851905889258995805458123 2777858833888493708187185)
                ·
                  refine ⟨2083394125416370281140389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2777858833888493708187185 2083394125416370281140389)
                  ·
                    refine ⟨390636398515569427713823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2083394125416370281140389 390636398515569427713823)
                    ·
                      rfl

theorem cell23_2282285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_2282285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282285 prefixEnd_2282285 := by exact prefixLift 2282285
  have htrace : WordTrace (prefixWord ++ tailWord_2282285) baseStart_2282285 baseEnd_2282285 := by
    simpa [prefixWord, tailWord_2282285, baseEnd_2282285] using wordTrace_append hprefix tailTrace_2282285
  have hstable : (prefixWord ++ tailWord_2282285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282285).length < 2 ^ (prefixWord ++ tailWord_2282285).sum := by decide
  have hdescent : baseEnd_2282285 < baseStart_2282285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282320 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 9]
def baseStart_2282320 : Nat := 118140960795 + 2282320 * 2 ^ 59
def prefixEnd_2282320 : Nat := 4983230072969 + 3 ^ 40 * 2282320 * 2
def baseEnd_2282320 : Nat := 130214129707735071800423

theorem tailTrace_2282320 : CollatzResearch.WordTrace tailWord_2282320 prefixEnd_2282320 130214129707735071800423 := by
  unfold tailWord_2282320
  simp only [CollatzResearch.WordTrace]
  refine ⟨41621524545775952034202207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55495366061034602712269609 41621524545775952034202207)
  ·
    refine ⟨62432286818663928051303311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41621524545775952034202207 62432286818663928051303311)
    ·
      refine ⟨93648430227995892076954967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62432286818663928051303311 93648430227995892076954967)
      ·
        refine ⟨140472645341993838115432451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93648430227995892076954967 140472645341993838115432451)
        ·
          refine ⟨210708968012990757173148677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140472645341993838115432451 210708968012990757173148677)
          ·
            refine ⟨39507931502435766969965377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 210708968012990757173148677 39507931502435766969965377)
            ·
              refine ⟨29630948626826825227474033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39507931502435766969965377 29630948626826825227474033)
              ·
                refine ⟨22223211470120118920605525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29630948626826825227474033 22223211470120118920605525)
                ·
                  refine ⟨130214129707735071800423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22223211470120118920605525 130214129707735071800423)
                  ·
                    rfl

theorem cell23_2282320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 9].length) (baseStart_2282320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282320 prefixEnd_2282320 := by exact prefixLift 2282320
  have htrace : WordTrace (prefixWord ++ tailWord_2282320) baseStart_2282320 baseEnd_2282320 := by
    simpa [prefixWord, tailWord_2282320, baseEnd_2282320] using wordTrace_append hprefix tailTrace_2282320
  have hstable : (prefixWord ++ tailWord_2282320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282320).length < 2 ^ (prefixWord ++ tailWord_2282320).sum := by decide
  have hdescent : baseEnd_2282320 < baseStart_2282320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282347 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 3]
def baseStart_2282347 : Nat := 118140960795 + 2282347 * 2 ^ 59
def prefixEnd_2282347 : Nat := 4983230072969 + 3 ^ 40 * 2282347 * 2
def baseEnd_2282347 : Nat := 1171941031347287040566183

theorem tailTrace_2282347 : CollatzResearch.WordTrace tailWord_2282347 prefixEnd_2282347 1171941031347287040566183 := by
  unfold tailWord_2282347
  simp only [CollatzResearch.WordTrace]
  refine ⟨83244033862454087679637295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55496022574969391786424863 83244033862454087679637295)
  ·
    refine ⟨124866050793681131519455943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83244033862454087679637295 124866050793681131519455943)
    ·
      refine ⟨187299076190521697279183915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124866050793681131519455943 187299076190521697279183915)
      ·
        refine ⟨280948614285782545918775873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187299076190521697279183915 280948614285782545918775873)
        ·
          refine ⟨210711460714336909439081905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280948614285782545918775873 210711460714336909439081905)
          ·
            refine ⟨158033595535752682079311429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210711460714336909439081905 158033595535752682079311429)
            ·
              refine ⟨29631299162953627889870893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 158033595535752682079311429 29631299162953627889870893)
              ·
                refine ⟨11111737186107610458701585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29631299162953627889870893 11111737186107610458701585)
                ·
                  refine ⟨8333802889580707844026189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11111737186107610458701585 8333802889580707844026189)
                  ·
                    refine ⟨3125176083592765441509821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8333802889580707844026189 3125176083592765441509821)
                    ·
                      refine ⟨1171941031347287040566183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3125176083592765441509821 1171941031347287040566183)
                      ·
                        rfl

theorem cell23_2282347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 3].length) (baseStart_2282347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282347 prefixEnd_2282347 := by exact prefixLift 2282347
  have htrace : WordTrace (prefixWord ++ tailWord_2282347) baseStart_2282347 baseEnd_2282347 := by
    simpa [prefixWord, tailWord_2282347, baseEnd_2282347] using wordTrace_append hprefix tailTrace_2282347
  have hstable : (prefixWord ++ tailWord_2282347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282347).length < 2 ^ (prefixWord ++ tailWord_2282347).sum := by decide
  have hdescent : baseEnd_2282347 < baseStart_2282347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282367 : List Nat := [1, 1, 2, 2, 1, 1, 5, 3, 2, 5]
def baseStart_2282367 : Nat := 118140960795 + 2282367 * 2 ^ 59
def prefixEnd_2282367 : Nat := 4983230072969 + 3 ^ 40 * 2282367 * 2
def baseEnd_2282367 : Nat := 390650433653458987438697

theorem tailTrace_2282367 : CollatzResearch.WordTrace tailWord_2282367 prefixEnd_2282367 390650433653458987438697 := by
  unfold tailWord_2282367
  simp only [CollatzResearch.WordTrace]
  refine ⟨83244763322381631095365355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55496508881587754063576903 83244763322381631095365355)
  ·
    refine ⟨124867144983572446643048033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83244763322381631095365355 124867144983572446643048033)
    ·
      refine ⟨93650358737679334982286025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124867144983572446643048033 93650358737679334982286025)
      ·
        refine ⟨70237769053259501236714519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93650358737679334982286025 70237769053259501236714519)
        ·
          refine ⟨105356653579889251855071779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70237769053259501236714519 105356653579889251855071779)
          ·
            refine ⟨158034980369833877782607669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105356653579889251855071779 158034980369833877782607669)
            ·
              refine ⟨14815779409671926042119469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 158034980369833877782607669 14815779409671926042119469)
              ·
                refine ⟨5555917278626972265794801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14815779409671926042119469 5555917278626972265794801)
                ·
                  refine ⟨4166937958970229199346101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5555917278626972265794801 4166937958970229199346101)
                  ·
                    refine ⟨390650433653458987438697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4166937958970229199346101 390650433653458987438697)
                    ·
                      rfl

theorem cell23_2282367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 5].length) (baseStart_2282367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282367 prefixEnd_2282367 := by exact prefixLift 2282367
  have htrace : WordTrace (prefixWord ++ tailWord_2282367) baseStart_2282367 baseEnd_2282367 := by
    simpa [prefixWord, tailWord_2282367, baseEnd_2282367] using wordTrace_append hprefix tailTrace_2282367
  have hstable : (prefixWord ++ tailWord_2282367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282367).length < 2 ^ (prefixWord ++ tailWord_2282367).sum := by decide
  have hdescent : baseEnd_2282367 < baseStart_2282367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282377 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 1, 2, 5]
def baseStart_2282377 : Nat := 118140960795 + 2282377 * 2 ^ 59
def prefixEnd_2282377 : Nat := 4983230072969 + 3 ^ 40 * 2282377 * 2
def baseEnd_2282377 : Nat := 1171956435766921923191045

theorem tailTrace_2282377 : CollatzResearch.WordTrace tailWord_2282377 prefixEnd_2282377 1171956435766921923191045 := by
  unfold tailWord_2282377
  simp only [CollatzResearch.WordTrace]
  refine ⟨83245128052345402803229385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55496752034896935202152923 83245128052345402803229385)
  ·
    refine ⟨62433846039259052102422039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83245128052345402803229385 62433846039259052102422039)
    ·
      refine ⟨93650769058888578153633059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62433846039259052102422039 93650769058888578153633059)
      ·
        refine ⟨140476153588332867230449589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93650769058888578153633059 140476153588332867230449589)
        ·
          refine ⟨13169639398906206302854649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140476153588332867230449589 13169639398906206302854649)
          ·
            refine ⟨9877229549179654727140987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13169639398906206302854649 9877229549179654727140987)
            ·
              refine ⟨14815844323769482090711481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9877229549179654727140987 14815844323769482090711481)
              ·
                refine ⟨11111883242827111568033611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14815844323769482090711481 11111883242827111568033611)
                ·
                  refine ⟨16667824864240667352050417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11111883242827111568033611 16667824864240667352050417)
                  ·
                    refine ⟨12500868648180500514037813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16667824864240667352050417 12500868648180500514037813)
                    ·
                      refine ⟨1171956435766921923191045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12500868648180500514037813 1171956435766921923191045)
                      ·
                        rfl

theorem cell23_2282377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_2282377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282377 prefixEnd_2282377 := by exact prefixLift 2282377
  have htrace : WordTrace (prefixWord ++ tailWord_2282377) baseStart_2282377 baseEnd_2282377 := by
    simpa [prefixWord, tailWord_2282377, baseEnd_2282377] using wordTrace_append hprefix tailTrace_2282377
  have hstable : (prefixWord ++ tailWord_2282377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282377).length < 2 ^ (prefixWord ++ tailWord_2282377).sum := by decide
  have hdescent : baseEnd_2282377 < baseStart_2282377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282387 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 4]
def baseStart_2282387 : Nat := 118140960795 + 2282387 * 2 ^ 59
def prefixEnd_2282387 : Nat := 4983230072969 + 3 ^ 40 * 2282387 * 2
def baseEnd_2282387 : Nat := 1171961570573466884065999

theorem tailTrace_2282387 : CollatzResearch.WordTrace tailWord_2282387 prefixEnd_2282387 1171961570573466884065999 := by
  unfold tailWord_2282387
  simp only [CollatzResearch.WordTrace]
  refine ⟨83245492782309174511093415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55496995188206116340728943 83245492782309174511093415)
  ·
    refine ⟨124868239173463761766640123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83245492782309174511093415 124868239173463761766640123)
    ·
      refine ⟨187302358760195642649960185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124868239173463761766640123 187302358760195642649960185)
      ·
        refine ⟨140476769070146731987470139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187302358760195642649960185 140476769070146731987470139)
        ·
          refine ⟨210715153605220097981205209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140476769070146731987470139 210715153605220097981205209)
          ·
            refine ⟨158036365203915073485903907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210715153605220097981205209 158036365203915073485903907)
            ·
              refine ⟨237054547805872610228855861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158036365203915073485903907 237054547805872610228855861)
              ·
                refine ⟨22223863856800557208955237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 237054547805872610228855861 22223863856800557208955237)
                ·
                  refine ⟨4166974473150104476679107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22223863856800557208955237 4166974473150104476679107)
                  ·
                    refine ⟨6250461709725156715018661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4166974473150104476679107 6250461709725156715018661)
                    ·
                      refine ⟨1171961570573466884065999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6250461709725156715018661 1171961570573466884065999)
                      ·
                        rfl

theorem cell23_2282387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 4].length) (baseStart_2282387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282387 prefixEnd_2282387 := by exact prefixLift 2282387
  have htrace : WordTrace (prefixWord ++ tailWord_2282387) baseStart_2282387 baseEnd_2282387 := by
    simpa [prefixWord, tailWord_2282387, baseEnd_2282387] using wordTrace_append hprefix tailTrace_2282387
  have hstable : (prefixWord ++ tailWord_2282387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282387).length < 2 ^ (prefixWord ++ tailWord_2282387).sum := by decide
  have hdescent : baseEnd_2282387 < baseStart_2282387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282422 : List Nat := [5, 1, 4, 1, 1, 1, 2, 3, 5]
def baseStart_2282422 : Nat := 118140960795 + 2282422 * 2 ^ 59
def prefixEnd_2282422 : Nat := 4983230072969 + 3 ^ 40 * 2282422 * 2
def baseEnd_2282422 : Nat := 130219949155152694125371

theorem tailTrace_2282422 : CollatzResearch.WordTrace tailWord_2282422 prefixEnd_2282422 130219949155152694125371 := by
  unfold tailWord_2282422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5202923083573898468038595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55497846224788250325745013 5202923083573898468038595)
  ·
    refine ⟨7804384625360847702057893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5202923083573898468038595 7804384625360847702057893)
    ·
      refine ⟨1463322117255158944135855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7804384625360847702057893 1463322117255158944135855)
      ·
        refine ⟨2194983175882738416203783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1463322117255158944135855 2194983175882738416203783)
        ·
          refine ⟨3292474763824107624305675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2194983175882738416203783 3292474763824107624305675)
          ·
            refine ⟨4938712145736161436458513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3292474763824107624305675 4938712145736161436458513)
            ·
              refine ⟨3704034109302121077343885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4938712145736161436458513 3704034109302121077343885)
              ·
                refine ⟨1389012790988295404003957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3704034109302121077343885 1389012790988295404003957)
                ·
                  refine ⟨130219949155152694125371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1389012790988295404003957 130219949155152694125371)
                  ·
                    rfl

theorem cell23_2282422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_2282422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282422 prefixEnd_2282422 := by exact prefixLift 2282422
  have htrace : WordTrace (prefixWord ++ tailWord_2282422) baseStart_2282422 baseEnd_2282422 := by
    simpa [prefixWord, tailWord_2282422, baseEnd_2282422] using wordTrace_append hprefix tailTrace_2282422
  have hstable : (prefixWord ++ tailWord_2282422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282422).length < 2 ^ (prefixWord ++ tailWord_2282422).sum := by decide
  have hdescent : baseEnd_2282422 < baseStart_2282422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282424 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 1, 4, 3]
def baseStart_2282424 : Nat := 118140960795 + 2282424 * 2 ^ 59
def prefixEnd_2282424 : Nat := 4983230072969 + 3 ^ 40 * 2282424 * 2
def baseEnd_2282424 : Nat := 1171980569357683239303329

theorem tailTrace_2282424 : CollatzResearch.WordTrace tailWord_2282424 prefixEnd_2282424 1171980569357683239303329 := by
  unfold tailWord_2282424
  simp only [CollatzResearch.WordTrace]
  refine ⟨41623421141587564915095163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55497894855450086553460217 41623421141587564915095163)
  ·
    refine ⟨62435131712381347372642745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41623421141587564915095163 62435131712381347372642745)
    ·
      refine ⟨46826348784286010529482059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62435131712381347372642745 46826348784286010529482059)
      ·
        refine ⟨70239523176429015794223089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46826348784286010529482059 70239523176429015794223089)
        ·
          refine ⟨52679642382321761845667317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70239523176429015794223089 52679642382321761845667317)
          ·
            refine ⟨4938716473342665173031311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52679642382321761845667317 4938716473342665173031311)
            ·
              refine ⟨7408074710013997759546967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4938716473342665173031311 7408074710013997759546967)
              ·
                refine ⟨11112112065020996639320451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7408074710013997759546967 11112112065020996639320451)
                ·
                  refine ⟨16668168097531494958980677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11112112065020996639320451 16668168097531494958980677)
                  ·
                    refine ⟨3125281518287155304808877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16668168097531494958980677 3125281518287155304808877)
                    ·
                      refine ⟨1171980569357683239303329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3125281518287155304808877 1171980569357683239303329)
                      ·
                        rfl

theorem cell23_2282424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_2282424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282424 prefixEnd_2282424 := by exact prefixLift 2282424
  have htrace : WordTrace (prefixWord ++ tailWord_2282424) baseStart_2282424 baseEnd_2282424 := by
    simpa [prefixWord, tailWord_2282424, baseEnd_2282424] using wordTrace_append hprefix tailTrace_2282424
  have hstable : (prefixWord ++ tailWord_2282424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282424).length < 2 ^ (prefixWord ++ tailWord_2282424).sum := by decide
  have hdescent : baseEnd_2282424 < baseStart_2282424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282447 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 6]
def baseStart_2282447 : Nat := 118140960795 + 2282447 * 2 ^ 59
def prefixEnd_2282447 : Nat := 4983230072969 + 3 ^ 40 * 2282447 * 2
def baseEnd_2282447 : Nat := 1171992379412736649315723

theorem tailTrace_2282447 : CollatzResearch.WordTrace tailWord_2282447 prefixEnd_2282447 1171992379412736649315723 := by
  unfold tailWord_2282447
  simp only [CollatzResearch.WordTrace]
  refine ⟨83247681162091804758277595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55498454108061203172185063 83247681162091804758277595)
  ·
    refine ⟨124871521743137707137416393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83247681162091804758277595 124871521743137707137416393)
    ·
      refine ⟨93653641307353280353062295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124871521743137707137416393 93653641307353280353062295)
      ·
        refine ⟨140480461961029920529593443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93653641307353280353062295 140480461961029920529593443)
        ·
          refine ⟨210720692941544880794390165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140480461961029920529593443 210720692941544880794390165)
          ·
            refine ⟨9877532481634916287237039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 210720692941544880794390165 9877532481634916287237039)
            ·
              refine ⟨14816298722452374430855559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9877532481634916287237039 14816298722452374430855559)
              ·
                refine ⟨22224448083678561646283339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14816298722452374430855559 22224448083678561646283339)
                ·
                  refine ⟨33336672125517842469425009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22224448083678561646283339 33336672125517842469425009)
                  ·
                    refine ⟨25002504094138381852068757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33336672125517842469425009 25002504094138381852068757)
                    ·
                      refine ⟨1171992379412736649315723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25002504094138381852068757 1171992379412736649315723)
                      ·
                        rfl

theorem cell23_2282447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_2282447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282447 prefixEnd_2282447 := by exact prefixLift 2282447
  have htrace : WordTrace (prefixWord ++ tailWord_2282447) baseStart_2282447 baseEnd_2282447 := by
    simpa [prefixWord, tailWord_2282447, baseEnd_2282447] using wordTrace_append hprefix tailTrace_2282447
  have hstable : (prefixWord ++ tailWord_2282447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282447).length < 2 ^ (prefixWord ++ tailWord_2282447).sum := by decide
  have hdescent : baseEnd_2282447 < baseStart_2282447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282481 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 1, 5, 2]
def baseStart_2282481 : Nat := 118140960795 + 2282481 * 2 ^ 59
def prefixEnd_2282481 : Nat := 4983230072969 + 3 ^ 40 * 2282481 * 2
def baseEnd_2282481 : Nat := 1172009837754989516290567

theorem tailTrace_2282481 : CollatzResearch.WordTrace tailWord_2282481 prefixEnd_2282481 1172009837754989516290567 := by
  unfold tailWord_2282481
  simp only [CollatzResearch.WordTrace]
  refine ⟨83248921243968628565015297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55499280829312419043343531 83248921243968628565015297)
  ·
    refine ⟨62436690932976471423761473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83248921243968628565015297 62436690932976471423761473)
    ·
      refine ⟨46827518199732353567821105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62436690932976471423761473 46827518199732353567821105)
      ·
        refine ⟨35120638649799265175865829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46827518199732353567821105 35120638649799265175865829)
        ·
          refine ⟨6585119746837362220474843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35120638649799265175865829 6585119746837362220474843)
          ·
            refine ⟨9877679620256043330712265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6585119746837362220474843 9877679620256043330712265)
            ·
              refine ⟨7408259715192032498034199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9877679620256043330712265 7408259715192032498034199)
              ·
                refine ⟨11112389572788048747051299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7408259715192032498034199 11112389572788048747051299)
                ·
                  refine ⟨16668584359182073120576949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11112389572788048747051299 16668584359182073120576949)
                  ·
                    refine ⟨1562679783673319355054089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16668584359182073120576949 1562679783673319355054089)
                    ·
                      refine ⟨1172009837754989516290567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1562679783673319355054089 1172009837754989516290567)
                      ·
                        rfl

theorem cell23_2282481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_2282481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282481 prefixEnd_2282481 := by exact prefixLift 2282481
  have htrace : WordTrace (prefixWord ++ tailWord_2282481) baseStart_2282481 baseEnd_2282481 := by
    simpa [prefixWord, tailWord_2282481, baseEnd_2282481] using wordTrace_append hprefix tailTrace_2282481
  have hstable : (prefixWord ++ tailWord_2282481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282481).length < 2 ^ (prefixWord ++ tailWord_2282481).sum := by decide
  have hdescent : baseEnd_2282481 < baseStart_2282481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282482 : List Nat := [3, 2, 1, 5, 1, 2, 1, 3, 1, 4]
def baseStart_2282482 : Nat := 118140960795 + 2282482 * 2 ^ 59
def prefixEnd_2282482 : Nat := 4983230072969 + 3 ^ 40 * 2282482 * 2
def baseEnd_2282482 : Nat := 390670117078548004126021

theorem tailTrace_2282482 : CollatzResearch.WordTrace tailWord_2282482 prefixEnd_2282482 390670117078548004126021 := by
  unfold tailWord_2282482
  simp only [CollatzResearch.WordTrace]
  refine ⟨20812239429241251433950425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55499305144643337157201133 20812239429241251433950425)
  ·
    refine ⟨15609179571930938575462819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20812239429241251433950425 15609179571930938575462819)
    ·
      refine ⟨23413769357896407863194229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15609179571930938575462819 23413769357896407863194229)
      ·
        refine ⟨2195040877302788237174459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23413769357896407863194229 2195040877302788237174459)
        ·
          refine ⟨3292561315954182355761689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2195040877302788237174459 3292561315954182355761689)
          ·
            refine ⟨2469420986965636766821267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3292561315954182355761689 2469420986965636766821267)
            ·
              refine ⟨3704131480448455150231901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469420986965636766821267 3704131480448455150231901)
              ·
                refine ⟨1389049305168170681336963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3704131480448455150231901 1389049305168170681336963)
                ·
                  refine ⟨2083573957752256022005445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1389049305168170681336963 2083573957752256022005445)
                  ·
                    refine ⟨390670117078548004126021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2083573957752256022005445 390670117078548004126021)
                    ·
                      rfl

theorem cell23_2282482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_2282482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282482 prefixEnd_2282482 := by exact prefixLift 2282482
  have htrace : WordTrace (prefixWord ++ tailWord_2282482) baseStart_2282482 baseEnd_2282482 := by
    simpa [prefixWord, tailWord_2282482, baseEnd_2282482] using wordTrace_append hprefix tailTrace_2282482
  have hstable : (prefixWord ++ tailWord_2282482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282482).length < 2 ^ (prefixWord ++ tailWord_2282482).sum := by decide
  have hdescent : baseEnd_2282482 < baseStart_2282482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282511 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 9, 2, 2]
def baseStart_2282511 : Nat := 118140960795 + 2282511 * 2 ^ 59
def prefixEnd_2282511 : Nat := 4983230072969 + 3 ^ 40 * 2282511 * 2
def baseEnd_2282511 : Nat := 1172025242174624398915429

theorem tailTrace_2282511 : CollatzResearch.WordTrace tailWord_2282511 prefixEnd_2282511 1172025242174624398915429 := by
  unfold tailWord_2282511
  simp only [CollatzResearch.WordTrace]
  refine ⟨83250015433859943688607387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55500010289239962459071591 83250015433859943688607387)
  ·
    refine ⟨124875023150789915532911081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83250015433859943688607387 124875023150789915532911081)
    ·
      refine ⟨93656267363092436649683311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124875023150789915532911081 93656267363092436649683311)
      ·
        refine ⟨140484401044638654974524967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93656267363092436649683311 140484401044638654974524967)
        ·
          refine ⟨210726601566957982461787451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140484401044638654974524967 210726601566957982461787451)
          ·
            refine ⟨316089902350436973692681177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210726601566957982461787451 316089902350436973692681177)
            ·
              refine ⟨237067426762827730269510883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316089902350436973692681177 237067426762827730269510883)
              ·
                refine ⟨355601140144241595404266325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237067426762827730269510883 355601140144241595404266325)
                ·
                  refine ⟨2083600430532665598071873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 355601140144241595404266325 2083600430532665598071873)
                  ·
                    refine ⟨1562700322899499198553905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2083600430532665598071873 1562700322899499198553905)
                    ·
                      refine ⟨1172025242174624398915429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1562700322899499198553905 1172025242174624398915429)
                      ·
                        rfl

theorem cell23_2282511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 2, 2].length) (baseStart_2282511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282511 prefixEnd_2282511 := by exact prefixLift 2282511
  have htrace : WordTrace (prefixWord ++ tailWord_2282511) baseStart_2282511 baseEnd_2282511 := by
    simpa [prefixWord, tailWord_2282511, baseEnd_2282511] using wordTrace_append hprefix tailTrace_2282511
  have hstable : (prefixWord ++ tailWord_2282511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282511).length < 2 ^ (prefixWord ++ tailWord_2282511).sum := by decide
  have hdescent : baseEnd_2282511 < baseStart_2282511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282525 : List Nat := [1, 4, 2, 2, 4, 1, 1, 2, 1, 5]
def baseStart_2282525 : Nat := 118140960795 + 2282525 * 2 ^ 59
def prefixEnd_2282525 : Nat := 4983230072969 + 3 ^ 40 * 2282525 * 2
def baseEnd_2282525 : Nat := 390677476967929114713455

theorem tailTrace_2282525 : CollatzResearch.WordTrace tailWord_2282525 prefixEnd_2282525 390677476967929114713455 := by
  unfold tailWord_2282525
  simp only [CollatzResearch.WordTrace]
  refine ⟨83250526055809224079617029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55500350703872816053078019 83250526055809224079617029)
  ·
    refine ⟨15609473635464229514928193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83250526055809224079617029 15609473635464229514928193)
    ·
      refine ⟨11707105226598172136196145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15609473635464229514928193 11707105226598172136196145)
      ·
        refine ⟨8780328919948629102147109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11707105226598172136196145 8780328919948629102147109)
        ·
          refine ⟨1646311672490367956652583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8780328919948629102147109 1646311672490367956652583)
          ·
            refine ⟨2469467508735551934978875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1646311672490367956652583 2469467508735551934978875)
            ·
              refine ⟨3704201263103327902468313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469467508735551934978875 3704201263103327902468313)
              ·
                refine ⟨2778150947327495926851235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3704201263103327902468313 2778150947327495926851235)
                ·
                  refine ⟨4167226420991243890276853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2778150947327495926851235 4167226420991243890276853)
                  ·
                    refine ⟨390677476967929114713455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4167226420991243890276853 390677476967929114713455)
                    ·
                      rfl

theorem cell23_2282525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_2282525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282525 prefixEnd_2282525 := by exact prefixLift 2282525
  have htrace : WordTrace (prefixWord ++ tailWord_2282525) baseStart_2282525 baseEnd_2282525 := by
    simpa [prefixWord, tailWord_2282525, baseEnd_2282525] using wordTrace_append hprefix tailTrace_2282525
  have hstable : (prefixWord ++ tailWord_2282525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282525).length < 2 ^ (prefixWord ++ tailWord_2282525).sum := by decide
  have hdescent : baseEnd_2282525 < baseStart_2282525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282528 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2282528 : Nat := 118140960795 + 2282528 * 2 ^ 59
def prefixEnd_2282528 : Nat := 4983230072969 + 3 ^ 40 * 2282528 * 2
def baseEnd_2282528 : Nat := 1172033971345750832402851

theorem tailTrace_2282528 : CollatzResearch.WordTrace tailWord_2282528 prefixEnd_2282528 1172033971345750832402851 := by
  unfold tailWord_2282528
  simp only [CollatzResearch.WordTrace]
  refine ⟨41625317737399177795988119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55500423649865570394650825 41625317737399177795988119)
  ·
    refine ⟨62437976606098766693982179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41625317737399177795988119 62437976606098766693982179)
    ·
      refine ⟨93656964909148150040973269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62437976606098766693982179 93656964909148150040973269)
      ·
        refine ⟨2195085115058159766585311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 93656964909148150040973269 2195085115058159766585311)
        ·
          refine ⟨3292627672587239649877967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2195085115058159766585311 3292627672587239649877967)
          ·
            refine ⟨4938941508880859474816951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3292627672587239649877967 4938941508880859474816951)
            ·
              refine ⟨7408412263321289212225427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4938941508880859474816951 7408412263321289212225427)
              ·
                refine ⟨11112618394981933818338141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7408412263321289212225427 11112618394981933818338141)
                ·
                  refine ⟨4167231898118225181876803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11112618394981933818338141 4167231898118225181876803)
                  ·
                    refine ⟨6250847847177337772815205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4167231898118225181876803 6250847847177337772815205)
                    ·
                      refine ⟨1172033971345750832402851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6250847847177337772815205 1172033971345750832402851)
                      ·
                        rfl

theorem cell23_2282528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2282528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282528 prefixEnd_2282528 := by exact prefixLift 2282528
  have htrace : WordTrace (prefixWord ++ tailWord_2282528) baseStart_2282528 baseEnd_2282528 := by
    simpa [prefixWord, tailWord_2282528, baseEnd_2282528] using wordTrace_append hprefix tailTrace_2282528
  have hstable : (prefixWord ++ tailWord_2282528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282528).length < 2 ^ (prefixWord ++ tailWord_2282528).sum := by decide
  have hdescent : baseEnd_2282528 < baseStart_2282528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282531 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 3]
def baseStart_2282531 : Nat := 118140960795 + 2282531 * 2 ^ 59
def prefixEnd_2282531 : Nat := 4983230072969 + 3 ^ 40 * 2282531 * 2
def baseEnd_2282531 : Nat := 1172035511787714320665337

theorem tailTrace_2282531 : CollatzResearch.WordTrace tailWord_2282531 prefixEnd_2282531 1172035511787714320665337 := by
  unfold tailWord_2282531
  simp only [CollatzResearch.WordTrace]
  refine ⟨83250744893787487104335447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55500496595858324736223631 83250744893787487104335447)
  ·
    refine ⟨124876117340681230656503171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83250744893787487104335447 124876117340681230656503171)
    ·
      refine ⟨187314176011021845984754757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124876117340681230656503171 187314176011021845984754757)
      ·
        refine ⟨35121408002066596122141517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187314176011021845984754757 35121408002066596122141517)
        ·
          refine ⟨13170528000774973545803069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35121408002066596122141517 13170528000774973545803069)
          ·
            refine ⟨4938948000290615079676151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13170528000774973545803069 4938948000290615079676151)
            ·
              refine ⟨7408422000435922619514227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4938948000290615079676151 7408422000435922619514227)
              ·
                refine ⟨11112633000653883929271341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7408422000435922619514227 11112633000653883929271341)
                ·
                  refine ⟨4167237375245206473476753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11112633000653883929271341 4167237375245206473476753)
                  ·
                    refine ⟨3125428031433904855107565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4167237375245206473476753 3125428031433904855107565)
                    ·
                      refine ⟨1172035511787714320665337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3125428031433904855107565 1172035511787714320665337)
                      ·
                        rfl

theorem cell23_2282531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_2282531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282531 prefixEnd_2282531 := by exact prefixLift 2282531
  have htrace : WordTrace (prefixWord ++ tailWord_2282531) baseStart_2282531 baseEnd_2282531 := by
    simpa [prefixWord, tailWord_2282531, baseEnd_2282531] using wordTrace_append hprefix tailTrace_2282531
  have hstable : (prefixWord ++ tailWord_2282531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282531).length < 2 ^ (prefixWord ++ tailWord_2282531).sum := by decide
  have hdescent : baseEnd_2282531 < baseStart_2282531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282545 : List Nat := [1, 2, 2, 3, 1, 2, 2, 5, 1, 2, 2]
def baseStart_2282545 : Nat := 118140960795 + 2282545 * 2 ^ 59
def prefixEnd_2282545 : Nat := 4983230072969 + 3 ^ 40 * 2282545 * 2
def baseEnd_2282545 : Nat := 1172042700516877265890273

theorem tailTrace_2282545 : CollatzResearch.WordTrace tailWord_2282545 prefixEnd_2282545 1172042700516877265890273 := by
  unfold tailWord_2282545
  simp only [CollatzResearch.WordTrace]
  refine ⟨83251255515736767495345089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55500837010491178330230059 83251255515736767495345089)
  ·
    refine ⟨62438441636802575621508817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83251255515736767495345089 62438441636802575621508817)
    ·
      refine ⟨46828831227601931716131613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62438441636802575621508817 46828831227601931716131613)
      ·
        refine ⟨17560811710350724393549355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46828831227601931716131613 17560811710350724393549355)
        ·
          refine ⟨26341217565526086590324033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17560811710350724393549355 26341217565526086590324033)
          ·
            refine ⟨19755913174144564942743025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26341217565526086590324033 19755913174144564942743025)
            ·
              refine ⟨14816934880608423707057269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19755913174144564942743025 14816934880608423707057269)
              ·
                refine ⟨1389087645057039722536619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14816934880608423707057269 1389087645057039722536619)
                ·
                  refine ⟨2083631467585559583804929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1389087645057039722536619 2083631467585559583804929)
                  ·
                    refine ⟨1562723600689169687853697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2083631467585559583804929 1562723600689169687853697)
                    ·
                      refine ⟨1172042700516877265890273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1562723600689169687853697 1172042700516877265890273)
                      ·
                        rfl

theorem cell23_2282545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_2282545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282545 prefixEnd_2282545 := by exact prefixLift 2282545
  have htrace : WordTrace (prefixWord ++ tailWord_2282545) baseStart_2282545 baseEnd_2282545 := by
    simpa [prefixWord, tailWord_2282545, baseEnd_2282545] using wordTrace_append hprefix tailTrace_2282545
  have hstable : (prefixWord ++ tailWord_2282545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282545).length < 2 ^ (prefixWord ++ tailWord_2282545).sum := by decide
  have hdescent : baseEnd_2282545 < baseStart_2282545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282548 : List Nat := [2, 5, 1, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_2282548 : Nat := 118140960795 + 2282548 * 2 ^ 59
def prefixEnd_2282548 : Nat := 4983230072969 + 3 ^ 40 * 2282548 * 2
def baseEnd_2282548 : Nat := 1172044240958840754152759

theorem tailTrace_2282548 : CollatzResearch.WordTrace tailWord_2282548 prefixEnd_2282548 1172044240958840754152759 := by
  unfold tailWord_2282548
  simp only [CollatzResearch.WordTrace]
  refine ⟨41625682467362949503852149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55500909956483932671802865 41625682467362949503852149)
  ·
    refine ⟨3902407731315276515986139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41625682467362949503852149 3902407731315276515986139)
    ·
      refine ⟨5853611596972914773979209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3902407731315276515986139 5853611596972914773979209)
      ·
        refine ⟨4390208697729686080484407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5853611596972914773979209 4390208697729686080484407)
        ·
          refine ⟨6585313046594529120726611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4390208697729686080484407 6585313046594529120726611)
          ·
            refine ⟨9877969569891793681089917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6585313046594529120726611 9877969569891793681089917)
            ·
              refine ⟨3704238588709422630408719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9877969569891793681089917 3704238588709422630408719)
              ·
                refine ⟨5556357883064133945613079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3704238588709422630408719 5556357883064133945613079)
                ·
                  refine ⟨8334536824596200918419619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5556357883064133945613079 8334536824596200918419619)
                  ·
                    refine ⟨12501805236894301377629429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8334536824596200918419619 12501805236894301377629429)
                    ·
                      refine ⟨1172044240958840754152759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12501805236894301377629429 1172044240958840754152759)
                      ·
                        rfl

theorem cell23_2282548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_2282548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282548 prefixEnd_2282548 := by exact prefixLift 2282548
  have htrace : WordTrace (prefixWord ++ tailWord_2282548) baseStart_2282548 baseEnd_2282548 := by
    simpa [prefixWord, tailWord_2282548, baseEnd_2282548] using wordTrace_append hprefix tailTrace_2282548
  have hstable : (prefixWord ++ tailWord_2282548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282548).length < 2 ^ (prefixWord ++ tailWord_2282548).sum := by decide
  have hdescent : baseEnd_2282548 < baseStart_2282548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282578 : List Nat := [3, 2, 2, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_2282578 : Nat := 118140960795 + 2282578 * 2 ^ 59
def prefixEnd_2282578 : Nat := 4983230072969 + 3 ^ 40 * 2282578 * 2
def baseEnd_2282578 : Nat := 1172059645378475636777621

theorem tailTrace_2282578 : CollatzResearch.WordTrace tailWord_2282578 prefixEnd_2282578 1172059645378475636777621 := by
  unfold tailWord_2282578
  simp only [CollatzResearch.WordTrace]
  refine ⟨20813114781154303532824097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55501639416411476087530925 20813114781154303532824097)
  ·
    refine ⟨15609836085865727649618073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20813114781154303532824097 15609836085865727649618073)
    ·
      refine ⟨11707377064399295737213555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15609836085865727649618073 11707377064399295737213555)
      ·
        refine ⟨17561065596598943605820333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11707377064399295737213555 17561065596598943605820333)
        ·
          refine ⟨6585399598724603852182625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17561065596598943605820333 6585399598724603852182625)
          ·
            refine ⟨4939049699043452889136969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6585399598724603852182625 4939049699043452889136969)
            ·
              refine ⟨3704287274282589666852727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4939049699043452889136969 3704287274282589666852727)
              ·
                refine ⟨5556430911423884500279091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3704287274282589666852727 5556430911423884500279091)
                ·
                  refine ⟨8334646367135826750418637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5556430911423884500279091 8334646367135826750418637)
                  ·
                    refine ⟨3125492387675935031406989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8334646367135826750418637 3125492387675935031406989)
                    ·
                      refine ⟨1172059645378475636777621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3125492387675935031406989 1172059645378475636777621)
                      ·
                        rfl

theorem cell23_2282578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_2282578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282578 prefixEnd_2282578 := by exact prefixLift 2282578
  have htrace : WordTrace (prefixWord ++ tailWord_2282578) baseStart_2282578 baseEnd_2282578 := by
    simpa [prefixWord, tailWord_2282578, baseEnd_2282578] using wordTrace_append hprefix tailTrace_2282578
  have hstable : (prefixWord ++ tailWord_2282578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282578).length < 2 ^ (prefixWord ++ tailWord_2282578).sum := by decide
  have hdescent : baseEnd_2282578 < baseStart_2282578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282584 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 2, 3, 4]
def baseStart_2282584 : Nat := 118140960795 + 2282584 * 2 ^ 59
def prefixEnd_2282584 : Nat := 4983230072969 + 3 ^ 40 * 2282584 * 2
def baseEnd_2282584 : Nat := 1172062726262402613302593

theorem tailTrace_2282584 : CollatzResearch.WordTrace tailWord_2282584 prefixEnd_2282584 1172062726262402613302593 := by
  unfold tailWord_2282584
  simp only [CollatzResearch.WordTrace]
  refine ⟨41626338981297738578007403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55501785308396984770676537 41626338981297738578007403)
  ·
    refine ⟨62439508471946607867011105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41626338981297738578007403 62439508471946607867011105)
    ·
      refine ⟨46829631353959955900258329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62439508471946607867011105 46829631353959955900258329)
      ·
        refine ⟨35122223515469966925193747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46829631353959955900258329 35122223515469966925193747)
        ·
          refine ⟨52683335273204950387790621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35122223515469966925193747 52683335273204950387790621)
          ·
            refine ⟨19756250727451856395421483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52683335273204950387790621 19756250727451856395421483)
            ·
              refine ⟨29634376091177784593132225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19756250727451856395421483 29634376091177784593132225)
              ·
                refine ⟨22225782068383338444849169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29634376091177784593132225 22225782068383338444849169)
                ·
                  refine ⟨16669336551287503833636877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22225782068383338444849169 16669336551287503833636877)
                  ·
                    refine ⟨6251001206732813937613829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16669336551287503833636877 6251001206732813937613829)
                    ·
                      refine ⟨1172062726262402613302593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6251001206732813937613829 1172062726262402613302593)
                      ·
                        rfl

theorem cell23_2282584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_2282584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282584 prefixEnd_2282584 := by exact prefixLift 2282584
  have htrace : WordTrace (prefixWord ++ tailWord_2282584) baseStart_2282584 baseEnd_2282584 := by
    simpa [prefixWord, tailWord_2282584, baseEnd_2282584] using wordTrace_append hprefix tailTrace_2282584
  have hstable : (prefixWord ++ tailWord_2282584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282584).length < 2 ^ (prefixWord ++ tailWord_2282584).sum := by decide
  have hdescent : baseEnd_2282584 < baseStart_2282584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282588 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_2282588 : Nat := 118140960795 + 2282588 * 2 ^ 59
def prefixEnd_2282588 : Nat := 4983230072969 + 3 ^ 40 * 2282588 * 2
def baseEnd_2282588 : Nat := 1172064780185020597652575

theorem tailTrace_2282588 : CollatzResearch.WordTrace tailWord_2282588 prefixEnd_2282588 1172064780185020597652575 := by
  unfold tailWord_2282588
  simp only [CollatzResearch.WordTrace]
  refine ⟨41626411927290492919580209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55501882569720657226106945 41626411927290492919580209)
  ·
    refine ⟨31219808945467869689685157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41626411927290492919580209 31219808945467869689685157)
    ·
      refine ⟨5853714177275225566815967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31219808945467869689685157 5853714177275225566815967)
      ·
        refine ⟨8780571265912838350223951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5853714177275225566815967 8780571265912838350223951)
        ·
          refine ⟨13170856898869257525335927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8780571265912838350223951 13170856898869257525335927)
          ·
            refine ⟨19756285348303886288003891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13170856898869257525335927 19756285348303886288003891)
            ·
              refine ⟨29634428022455829432005837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19756285348303886288003891 29634428022455829432005837)
              ·
                refine ⟨11112910508420936037002189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29634428022455829432005837 11112910508420936037002189)
                ·
                  refine ⟨4167341440657851013875821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11112910508420936037002189 4167341440657851013875821)
                  ·
                    refine ⟨1562753040246694130203433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4167341440657851013875821 1562753040246694130203433)
                    ·
                      refine ⟨1172064780185020597652575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1562753040246694130203433 1172064780185020597652575)
                      ·
                        rfl

theorem cell23_2282588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_2282588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282588 prefixEnd_2282588 := by exact prefixLift 2282588
  have htrace : WordTrace (prefixWord ++ tailWord_2282588) baseStart_2282588 baseEnd_2282588 := by
    simpa [prefixWord, tailWord_2282588, baseEnd_2282588] using wordTrace_append hprefix tailTrace_2282588
  have hstable : (prefixWord ++ tailWord_2282588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282588).length < 2 ^ (prefixWord ++ tailWord_2282588).sum := by decide
  have hdescent : baseEnd_2282588 < baseStart_2282588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282604 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 5]
def baseStart_2282604 : Nat := 118140960795 + 2282604 * 2 ^ 59
def prefixEnd_2282604 : Nat := 4983230072969 + 3 ^ 40 * 2282604 * 2
def baseEnd_2282604 : Nat := 1172072995875492535052501

theorem tailTrace_2282604 : CollatzResearch.WordTrace tailWord_2282604 prefixEnd_2282604 1172072995875492535052501 := by
  unfold tailWord_2282604
  simp only [CollatzResearch.WordTrace]
  refine ⟨41626703711261510285871433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55502271615015347047828577 41626703711261510285871433)
  ·
    refine ⟨31220027783446132714403575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41626703711261510285871433 31220027783446132714403575)
    ·
      refine ⟨46830041675169199071605363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31220027783446132714403575 46830041675169199071605363)
      ·
        refine ⟨70245062512753798607408045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46830041675169199071605363 70245062512753798607408045)
        ·
          refine ⟨26341898442282674477778017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70245062512753798607408045 26341898442282674477778017)
          ·
            refine ⟨19756423831712005858333513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26341898442282674477778017 19756423831712005858333513)
            ·
              refine ⟨14817317873784004393750135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19756423831712005858333513 14817317873784004393750135)
              ·
                refine ⟨22225976810676006590625203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14817317873784004393750135 22225976810676006590625203)
                ·
                  refine ⟨33338965216014009885937805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22225976810676006590625203 33338965216014009885937805)
                  ·
                    refine ⟨12502111956005253707226677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33338965216014009885937805 12502111956005253707226677)
                    ·
                      refine ⟨1172072995875492535052501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12502111956005253707226677 1172072995875492535052501)
                      ·
                        rfl

theorem cell23_2282604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_2282604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282604 prefixEnd_2282604 := by exact prefixLift 2282604
  have htrace : WordTrace (prefixWord ++ tailWord_2282604) baseStart_2282604 baseEnd_2282604 := by
    simpa [prefixWord, tailWord_2282604, baseEnd_2282604] using wordTrace_append hprefix tailTrace_2282604
  have hstable : (prefixWord ++ tailWord_2282604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282604).length < 2 ^ (prefixWord ++ tailWord_2282604).sum := by decide
  have hdescent : baseEnd_2282604 < baseStart_2282604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282605 : List Nat := [1, 5, 1, 1, 2, 3, 1, 3, 1, 3, 2]
def baseStart_2282605 : Nat := 118140960795 + 2282605 * 2 ^ 59
def prefixEnd_2282605 : Nat := 4983230072969 + 3 ^ 40 * 2282605 * 2
def baseEnd_2282605 : Nat := 1172073509356147031139997

theorem tailTrace_2282605 : CollatzResearch.WordTrace tailWord_2282605 prefixEnd_2282605 1172073509356147031139997 := by
  unfold tailWord_2282605
  simp only [CollatzResearch.WordTrace]
  refine ⟨83253443895519397742529269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55502295930346265161686179 83253443895519397742529269)
  ·
    refine ⟨7805010365204943538362119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83253443895519397742529269 7805010365204943538362119)
    ·
      refine ⟨11707515547807415307543179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7805010365204943538362119 11707515547807415307543179)
      ·
        refine ⟨17561273321711122961314769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11707515547807415307543179 17561273321711122961314769)
        ·
          refine ⟨13170954991283342220986077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17561273321711122961314769 13170954991283342220986077)
          ·
            refine ⟨4939108121731253332869779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13170954991283342220986077 4939108121731253332869779)
            ·
              refine ⟨7408662182596879999304669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4939108121731253332869779 7408662182596879999304669)
              ·
                refine ⟨2778248318473829999739251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7408662182596879999304669 2778248318473829999739251)
                ·
                  refine ⟨4167372477710744999608877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2778248318473829999739251 4167372477710744999608877)
                  ·
                    refine ⟨1562764679141529374853329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4167372477710744999608877 1562764679141529374853329)
                    ·
                      refine ⟨1172073509356147031139997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1562764679141529374853329 1172073509356147031139997)
                      ·
                        rfl

theorem cell23_2282605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_2282605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282605 prefixEnd_2282605 := by exact prefixLift 2282605
  have htrace : WordTrace (prefixWord ++ tailWord_2282605) baseStart_2282605 baseEnd_2282605 := by
    simpa [prefixWord, tailWord_2282605, baseEnd_2282605] using wordTrace_append hprefix tailTrace_2282605
  have hstable : (prefixWord ++ tailWord_2282605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282605).length < 2 ^ (prefixWord ++ tailWord_2282605).sum := by decide
  have hdescent : baseEnd_2282605 < baseStart_2282605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282624 : List Nat := [2, 1, 1, 2, 1, 3, 3, 3, 7]
def baseStart_2282624 : Nat := 118140960795 + 2282624 * 2 ^ 59
def prefixEnd_2282624 : Nat := 4983230072969 + 3 ^ 40 * 2282624 * 2
def baseEnd_2282624 : Nat := 130231473943175828533601

theorem tailTrace_2282624 : CollatzResearch.WordTrace tailWord_2282624 prefixEnd_2282624 130231473943175828533601 := by
  unfold tailWord_2282624
  simp only [CollatzResearch.WordTrace]
  refine ⟨41627068441225281993735463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55502757921633709324980617 41627068441225281993735463)
  ·
    refine ⟨62440602661837922990603195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41627068441225281993735463 62440602661837922990603195)
    ·
      refine ⟨93660903992756884485904793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62440602661837922990603195 93660903992756884485904793)
      ·
        refine ⟨70245677994567663364428595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93660903992756884485904793 70245677994567663364428595)
        ·
          refine ⟨105368516991851495046642893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70245677994567663364428595 105368516991851495046642893)
          ·
            refine ⟨39513193871944310642491085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105368516991851495046642893 39513193871944310642491085)
            ·
              refine ⟨14817447701979116490934157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39513193871944310642491085 14817447701979116490934157)
              ·
                refine ⟨5556542888242168684100309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14817447701979116490934157 5556542888242168684100309)
                ·
                  refine ⟨130231473943175828533601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5556542888242168684100309 130231473943175828533601)
                  ·
                    rfl

theorem cell23_2282624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 7].length) (baseStart_2282624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282624 prefixEnd_2282624 := by exact prefixLift 2282624
  have htrace : WordTrace (prefixWord ++ tailWord_2282624) baseStart_2282624 baseEnd_2282624 := by
    simpa [prefixWord, tailWord_2282624, baseEnd_2282624] using wordTrace_append hprefix tailTrace_2282624
  have hstable : (prefixWord ++ tailWord_2282624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282624).length < 2 ^ (prefixWord ++ tailWord_2282624).sum := by decide
  have hdescent : baseEnd_2282624 < baseStart_2282624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282681 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 1, 2, 5]
def baseStart_2282681 : Nat := 118140960795 + 2282681 * 2 ^ 59
def prefixEnd_2282681 : Nat := 4983230072969 + 3 ^ 40 * 2282681 * 2
def baseEnd_2282681 : Nat := 1172112533885888733789647

theorem tailTrace_2282681 : CollatzResearch.WordTrace tailWord_2282681 prefixEnd_2282681 1172112533885888733789647 := by
  unfold tailWord_2282681
  simp only [CollatzResearch.WordTrace]
  refine ⟨83256215843244062722295897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55504143895496041814863931 83256215843244062722295897)
  ·
    refine ⟨62442161882433047041721923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83256215843244062722295897 62442161882433047041721923)
    ·
      refine ⟨93663242823649570562582885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62442161882433047041721923 93663242823649570562582885)
      ·
        refine ⟨17561858029434294480484291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93663242823649570562582885 17561858029434294480484291)
        ·
          refine ⟨26342787044151441720726437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17561858029434294480484291 26342787044151441720726437)
          ·
            refine ⟨4939272570778395322636207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26342787044151441720726437 4939272570778395322636207)
            ·
              refine ⟨7408908856167592983954311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4939272570778395322636207 7408908856167592983954311)
              ·
                refine ⟨11113363284251389475931467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7408908856167592983954311 11113363284251389475931467)
                ·
                  refine ⟨16670044926377084213897201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11113363284251389475931467 16670044926377084213897201)
                  ·
                    refine ⟨12502533694782813160422901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16670044926377084213897201 12502533694782813160422901)
                    ·
                      refine ⟨1172112533885888733789647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12502533694782813160422901 1172112533885888733789647)
                      ·
                        rfl

theorem cell23_2282681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_2282681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282681 prefixEnd_2282681 := by exact prefixLift 2282681
  have htrace : WordTrace (prefixWord ++ tailWord_2282681) baseStart_2282681 baseEnd_2282681 := by
    simpa [prefixWord, tailWord_2282681, baseEnd_2282681] using wordTrace_append hprefix tailTrace_2282681
  have hstable : (prefixWord ++ tailWord_2282681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282681).length < 2 ^ (prefixWord ++ tailWord_2282681).sum := by decide
  have hdescent : baseEnd_2282681 < baseStart_2282681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282711 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 3]
def baseStart_2282711 : Nat := 118140960795 + 2282711 * 2 ^ 59
def prefixEnd_2282711 : Nat := 4983230072969 + 3 ^ 40 * 2282711 * 2
def baseEnd_2282711 : Nat := 1172127938305523616414509

theorem tailTrace_2282711 : CollatzResearch.WordTrace tailWord_2282711 prefixEnd_2282711 1172127938305523616414509 := by
  unfold tailWord_2282711
  simp only [CollatzResearch.WordTrace]
  refine ⟨83257310033135377845887987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55504873355423585230591991 83257310033135377845887987)
  ·
    refine ⟨124885965049703066768831981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83257310033135377845887987 124885965049703066768831981)
    ·
      refine ⟨46832236893638650038311993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124885965049703066768831981 46832236893638650038311993)
      ·
        refine ⟨35124177670228987528733995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46832236893638650038311993 35124177670228987528733995)
        ·
          refine ⟨52686266505343481293100993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35124177670228987528733995 52686266505343481293100993)
          ·
            refine ⟨39514699879007610969825745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52686266505343481293100993 39514699879007610969825745)
            ·
              refine ⟨29636024909255708227369309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39514699879007610969825745 29636024909255708227369309)
              ·
                refine ⟨11113509340970890585263491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29636024909255708227369309 11113509340970890585263491)
                ·
                  refine ⟨16670264011456335877895237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11113509340970890585263491 16670264011456335877895237)
                  ·
                    refine ⟨3125674502148062977105357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16670264011456335877895237 3125674502148062977105357)
                    ·
                      refine ⟨1172127938305523616414509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3125674502148062977105357 1172127938305523616414509)
                      ·
                        rfl

theorem cell23_2282711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_2282711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282711 prefixEnd_2282711 := by exact prefixLift 2282711
  have htrace : WordTrace (prefixWord ++ tailWord_2282711) baseStart_2282711 baseEnd_2282711 := by
    simpa [prefixWord, tailWord_2282711, baseEnd_2282711] using wordTrace_append hprefix tailTrace_2282711
  have hstable : (prefixWord ++ tailWord_2282711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282711).length < 2 ^ (prefixWord ++ tailWord_2282711).sum := by decide
  have hdescent : baseEnd_2282711 < baseStart_2282711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282728 : List Nat := [2, 1, 4, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_2282728 : Nat := 118140960795 + 2282728 * 2 ^ 59
def prefixEnd_2282728 : Nat := 4983230072969 + 3 ^ 40 * 2282728 * 2
def baseEnd_2282728 : Nat := 1172136667476650049901931

theorem tailTrace_2282728 : CollatzResearch.WordTrace tailWord_2282728 prefixEnd_2282728 1172136667476650049901931 := by
  unfold tailWord_2282728
  simp only [CollatzResearch.WordTrace]
  refine ⟨41628965037036894874628419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55505286716049193166171225 41628965037036894874628419)
  ·
    refine ⟨62443447555555342311942629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41628965037036894874628419 62443447555555342311942629)
    ·
      refine ⟨11708146416666626683489243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62443447555555342311942629 11708146416666626683489243)
      ·
        refine ⟨17562219624999940025233865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11708146416666626683489243 17562219624999940025233865)
        ·
          refine ⟨13171664718749955018925399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17562219624999940025233865 13171664718749955018925399)
          ·
            refine ⟨19757497078124932528388099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13171664718749955018925399 19757497078124932528388099)
            ·
              refine ⟨29636245617187398792582149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19757497078124932528388099 29636245617187398792582149)
              ·
                refine ⟨5556796053222637273609153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29636245617187398792582149 5556796053222637273609153)
                ·
                  refine ⟨4167597039916977955206865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5556796053222637273609153 4167597039916977955206865)
                  ·
                    refine ⟨3125697779937733466405149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4167597039916977955206865 3125697779937733466405149)
                    ·
                      refine ⟨1172136667476650049901931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3125697779937733466405149 1172136667476650049901931)
                      ·
                        rfl

theorem cell23_2282728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_2282728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282728 prefixEnd_2282728 := by exact prefixLift 2282728
  have htrace : WordTrace (prefixWord ++ tailWord_2282728) baseStart_2282728 baseEnd_2282728 := by
    simpa [prefixWord, tailWord_2282728, baseEnd_2282728] using wordTrace_append hprefix tailTrace_2282728
  have hstable : (prefixWord ++ tailWord_2282728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282728).length < 2 ^ (prefixWord ++ tailWord_2282728).sum := by decide
  have hdescent : baseEnd_2282728 < baseStart_2282728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282731 : List Nat := [1, 1, 1, 1, 2, 6, 1, 4, 6]
def baseStart_2282731 : Nat := 118140960795 + 2282731 * 2 ^ 59
def prefixEnd_2282731 : Nat := 4983230072969 + 3 ^ 40 * 2282731 * 2
def baseEnd_2282731 : Nat := 130237578657623726462713

theorem tailTrace_2282731 : CollatzResearch.WordTrace tailWord_2282731 prefixEnd_2282731 130237578657623726462713 := by
  unfold tailWord_2282731
  simp only [CollatzResearch.WordTrace]
  refine ⟨83258039493062921261616047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55505359662041947507744031 83258039493062921261616047)
  ·
    refine ⟨124887059239594381892424071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83258039493062921261616047 124887059239594381892424071)
    ·
      refine ⟨187330588859391572838636107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124887059239594381892424071 187330588859391572838636107)
      ·
        refine ⟨280995883289087359257954161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187330588859391572838636107 280995883289087359257954161)
        ·
          refine ⟨210746912466815519443465621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280995883289087359257954161 210746912466815519443465621)
          ·
            refine ⟨9878761521881977473912451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 210746912466815519443465621 9878761521881977473912451)
            ·
              refine ⟨14818142282822966210868677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9878761521881977473912451 14818142282822966210868677)
              ·
                refine ⟨2778401678029306164537877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14818142282822966210868677 2778401678029306164537877)
                ·
                  refine ⟨130237578657623726462713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2778401678029306164537877 130237578657623726462713)
                  ·
                    rfl

theorem cell23_2282731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 6].length) (baseStart_2282731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282731 prefixEnd_2282731 := by exact prefixLift 2282731
  have htrace : WordTrace (prefixWord ++ tailWord_2282731) baseStart_2282731 baseEnd_2282731 := by
    simpa [prefixWord, tailWord_2282731, baseEnd_2282731] using wordTrace_append hprefix tailTrace_2282731
  have hstable : (prefixWord ++ tailWord_2282731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282731).length < 2 ^ (prefixWord ++ tailWord_2282731).sum := by decide
  have hdescent : baseEnd_2282731 < baseStart_2282731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282761 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 3, 5]
def baseStart_2282761 : Nat := 118140960795 + 2282761 * 2 ^ 59
def prefixEnd_2282761 : Nat := 4983230072969 + 3 ^ 40 * 2282761 * 2
def baseEnd_2282761 : Nat := 390717870779416140263093

theorem tailTrace_2282761 : CollatzResearch.WordTrace tailWord_2282761 prefixEnd_2282761 390717870779416140263093 := by
  unfold tailWord_2282761
  simp only [CollatzResearch.WordTrace]
  refine ⟨83259133682954236385208137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55506089121969490923472091 83259133682954236385208137)
  ·
    refine ⟨62444350262215677288906103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83259133682954236385208137 62444350262215677288906103)
    ·
      refine ⟨93666525393323515933359155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62444350262215677288906103 93666525393323515933359155)
      ·
        refine ⟨140499788089985273900038733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93666525393323515933359155 140499788089985273900038733)
        ·
          refine ⟨52687420533744477712514525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140499788089985273900038733 52687420533744477712514525)
          ·
            refine ⟨19757782700154179142192947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52687420533744477712514525 19757782700154179142192947)
            ·
              refine ⟨29636674050231268713289421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19757782700154179142192947 29636674050231268713289421)
              ·
                refine ⟨11113752768836725767483533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29636674050231268713289421 11113752768836725767483533)
                ·
                  refine ⟨4167657288313772162806325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11113752768836725767483533 4167657288313772162806325)
                  ·
                    refine ⟨390717870779416140263093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4167657288313772162806325 390717870779416140263093)
                    ·
                      rfl

theorem cell23_2282761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 5].length) (baseStart_2282761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282761 prefixEnd_2282761 := by exact prefixLift 2282761
  have htrace : WordTrace (prefixWord ++ tailWord_2282761) baseStart_2282761 baseEnd_2282761 := by
    simpa [prefixWord, tailWord_2282761, baseEnd_2282761] using wordTrace_append hprefix tailTrace_2282761
  have hstable : (prefixWord ++ tailWord_2282761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282761).length < 2 ^ (prefixWord ++ tailWord_2282761).sum := by decide
  have hdescent : baseEnd_2282761 < baseStart_2282761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282792 : List Nat := [2, 1, 5, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_2282792 : Nat := 118140960795 + 2282792 * 2 ^ 59
def prefixEnd_2282792 : Nat := 4983230072969 + 3 ^ 40 * 2282792 * 2
def baseEnd_2282792 : Nat := 1172169530238537799501637

theorem tailTrace_2282792 : CollatzResearch.WordTrace tailWord_2282792 prefixEnd_2282792 1172169530238537799501637 := by
  unfold tailWord_2282792
  simp only [CollatzResearch.WordTrace]
  refine ⟨41630132172920964339793315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55506842897227952453057753 41630132172920964339793315)
  ·
    refine ⟨62445198259381446509689973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41630132172920964339793315 62445198259381446509689973)
    ·
      refine ⟨5854237336817010610283435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62445198259381446509689973 5854237336817010610283435)
      ·
        refine ⟨8781356005225515915425153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5854237336817010610283435 8781356005225515915425153)
        ·
          refine ⟨6586017003919136936568865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8781356005225515915425153 6586017003919136936568865)
          ·
            refine ⟨4939512752939352702426649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6586017003919136936568865 4939512752939352702426649)
            ·
              refine ⟨3704634564704514526819987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4939512752939352702426649 3704634564704514526819987)
              ·
                refine ⟨5556951847056771790229981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3704634564704514526819987 5556951847056771790229981)
                ·
                  refine ⟨2083856942646289421336243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5556951847056771790229981 2083856942646289421336243)
                  ·
                    refine ⟨3125785413969434132004365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2083856942646289421336243 3125785413969434132004365)
                    ·
                      refine ⟨1172169530238537799501637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3125785413969434132004365 1172169530238537799501637)
                      ·
                        rfl

theorem cell23_2282792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_2282792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282792 prefixEnd_2282792 := by exact prefixLift 2282792
  have htrace : WordTrace (prefixWord ++ tailWord_2282792) baseStart_2282792 baseEnd_2282792 := by
    simpa [prefixWord, tailWord_2282792, baseEnd_2282792] using wordTrace_append hprefix tailTrace_2282792
  have hstable : (prefixWord ++ tailWord_2282792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282792).length < 2 ^ (prefixWord ++ tailWord_2282792).sum := by decide
  have hdescent : baseEnd_2282792 < baseStart_2282792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282815 : List Nat := [1, 1, 2, 2, 4, 3, 2, 2, 1, 1, 4]
def baseStart_2282815 : Nat := 118140960795 + 2282815 * 2 ^ 59
def prefixEnd_2282815 : Nat := 4983230072969 + 3 ^ 40 * 2282815 * 2
def baseEnd_2282815 : Nat := 1172181340293591209514031

theorem tailTrace_2282815 : CollatzResearch.WordTrace tailWord_2282815 prefixEnd_2282815 1172181340293591209514031 := by
  unfold tailWord_2282815
  simp only [CollatzResearch.WordTrace]
  refine ⟨83261103224758603607673899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55507402149839069071782599 83261103224758603607673899)
  ·
    refine ⟨124891654837137905411510849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83261103224758603607673899 124891654837137905411510849)
    ·
      refine ⟨93668741127853429058633137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124891654837137905411510849 93668741127853429058633137)
      ·
        refine ⟨70251555845890071793974853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93668741127853429058633137 70251555845890071793974853)
        ·
          refine ⟨13172166721104388461370285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70251555845890071793974853 13172166721104388461370285)
          ·
            refine ⟨4939562520414145673013857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13172166721104388461370285 4939562520414145673013857)
            ·
              refine ⟨3704671890310609254760393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4939562520414145673013857 3704671890310609254760393)
              ·
                refine ⟨2778503917732956941070295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3704671890310609254760393 2778503917732956941070295)
                ·
                  refine ⟨4167755876599435411605443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2778503917732956941070295 4167755876599435411605443)
                  ·
                    refine ⟨6251633814899153117408165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4167755876599435411605443 6251633814899153117408165)
                    ·
                      refine ⟨1172181340293591209514031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6251633814899153117408165 1172181340293591209514031)
                      ·
                        rfl

theorem cell23_2282815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 1, 4].length) (baseStart_2282815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282815 prefixEnd_2282815 := by exact prefixLift 2282815
  have htrace : WordTrace (prefixWord ++ tailWord_2282815) baseStart_2282815 baseEnd_2282815 := by
    simpa [prefixWord, tailWord_2282815, baseEnd_2282815] using wordTrace_append hprefix tailTrace_2282815
  have hstable : (prefixWord ++ tailWord_2282815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282815).length < 2 ^ (prefixWord ++ tailWord_2282815).sum := by decide
  have hdescent : baseEnd_2282815 < baseStart_2282815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282869 : List Nat := [1, 3, 4, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_2282869 : Nat := 118140960795 + 2282869 * 2 ^ 59
def prefixEnd_2282869 : Nat := 4983230072969 + 3 ^ 40 * 2282869 * 2
def baseEnd_2282869 : Nat := 1172209068248933998238783

theorem tailTrace_2282869 : CollatzResearch.WordTrace tailWord_2282869 prefixEnd_2282869 1172209068248933998238783 := by
  unfold tailWord_2282869
  simp only [CollatzResearch.WordTrace]
  refine ⟨83263072766562970830139661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55508715177708647220093107 83263072766562970830139661)
  ·
    refine ⟨31223652287461114061302373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83263072766562970830139661 31223652287461114061302373)
    ·
      refine ⟨5854434803898958886494195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31223652287461114061302373 5854434803898958886494195)
      ·
        refine ⟨8781652205848438329741293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5854434803898958886494195 8781652205848438329741293)
        ·
          refine ⟨3293119577193164373652985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8781652205848438329741293 3293119577193164373652985)
          ·
            refine ⟨2469839682894873280239739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3293119577193164373652985 2469839682894873280239739)
            ·
              refine ⟨3704759524342309920359609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469839682894873280239739 3704759524342309920359609)
              ·
                refine ⟨2778569643256732440269707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3704759524342309920359609 2778569643256732440269707)
                ·
                  refine ⟨4167854464885098660404561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2778569643256732440269707 4167854464885098660404561)
                  ·
                    refine ⟨3125890848663823995303421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4167854464885098660404561 3125890848663823995303421)
                    ·
                      refine ⟨1172209068248933998238783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3125890848663823995303421 1172209068248933998238783)
                      ·
                        rfl

theorem cell23_2282869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_2282869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282869 prefixEnd_2282869 := by exact prefixLift 2282869
  have htrace : WordTrace (prefixWord ++ tailWord_2282869) baseStart_2282869 baseEnd_2282869 := by
    simpa [prefixWord, tailWord_2282869, baseEnd_2282869] using wordTrace_append hprefix tailTrace_2282869
  have hstable : (prefixWord ++ tailWord_2282869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282869).length < 2 ^ (prefixWord ++ tailWord_2282869).sum := by decide
  have hdescent : baseEnd_2282869 < baseStart_2282869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282875 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 3, 3, 2]
def baseStart_2282875 : Nat := 118140960795 + 2282875 * 2 ^ 59
def prefixEnd_2282875 : Nat := 4983230072969 + 3 ^ 40 * 2282875 * 2
def baseEnd_2282875 : Nat := 1172212149132860974763755

theorem tailTrace_2282875 : CollatzResearch.WordTrace tailWord_2282875 prefixEnd_2282875 1172212149132860974763755 := by
  unfold tailWord_2282875
  simp only [CollatzResearch.WordTrace]
  refine ⟨83263291604541233854858079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55508861069694155903238719 83263291604541233854858079)
  ·
    refine ⟨124894937406811850782287119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83263291604541233854858079 124894937406811850782287119)
    ·
      refine ⟨187342406110217776173430679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124894937406811850782287119 187342406110217776173430679)
      ·
        refine ⟨281013609165326664260146019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187342406110217776173430679 281013609165326664260146019)
        ·
          refine ⟨421520413747989996390219029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281013609165326664260146019 421520413747989996390219029)
          ·
            refine ⟨19758769394437031080791517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 421520413747989996390219029 19758769394437031080791517)
            ·
              refine ⟨7409538522913886655296819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19758769394437031080791517 7409538522913886655296819)
              ·
                refine ⟨11114307784370829982945229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7409538522913886655296819 11114307784370829982945229)
                ·
                  refine ⟨4167865419139061243604461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11114307784370829982945229 4167865419139061243604461)
                  ·
                    refine ⟨1562949532177147966351673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4167865419139061243604461 1562949532177147966351673)
                    ·
                      refine ⟨1172212149132860974763755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1562949532177147966351673 1172212149132860974763755)
                      ·
                        rfl

theorem cell23_2282875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 3, 2].length) (baseStart_2282875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282875 prefixEnd_2282875 := by exact prefixLift 2282875
  have htrace : WordTrace (prefixWord ++ tailWord_2282875) baseStart_2282875 baseEnd_2282875 := by
    simpa [prefixWord, tailWord_2282875, baseEnd_2282875] using wordTrace_append hprefix tailTrace_2282875
  have hstable : (prefixWord ++ tailWord_2282875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282875).length < 2 ^ (prefixWord ++ tailWord_2282875).sum := by decide
  have hdescent : baseEnd_2282875 < baseStart_2282875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282882 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_2282882 : Nat := 118140960795 + 2282882 * 2 ^ 59
def prefixEnd_2282882 : Nat := 4983230072969 + 3 ^ 40 * 2282882 * 2
def baseEnd_2282882 : Nat := 1172215743497442447376223

theorem tailTrace_2282882 : CollatzResearch.WordTrace tailWord_2282882 prefixEnd_2282882 1172215743497442447376223 := by
  unfold tailWord_2282882
  simp only [CollatzResearch.WordTrace]
  refine ⟨20815886728878968512590725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55509031277010582700241933 20815886728878968512590725)
  ·
    refine ⟨3902978761664806596110761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20815886728878968512590725 3902978761664806596110761)
    ·
      refine ⟨2927234071248604947083071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3902978761664806596110761 2927234071248604947083071)
      ·
        refine ⟨4390851106872907420624607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2927234071248604947083071 4390851106872907420624607)
        ·
          refine ⟨6586276660309361130936911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4390851106872907420624607 6586276660309361130936911)
          ·
            refine ⟨9879414990464041696405367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6586276660309361130936911 9879414990464041696405367)
            ·
              refine ⟨14819122485696062544608051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9879414990464041696405367 14819122485696062544608051)
              ·
                refine ⟨22228683728544093816912077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14819122485696062544608051 22228683728544093816912077)
                ·
                  refine ⟨8335756398204035181342029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22228683728544093816912077 8335756398204035181342029)
                  ·
                    refine ⟨3125908649326513193003261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8335756398204035181342029 3125908649326513193003261)
                    ·
                      refine ⟨1172215743497442447376223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3125908649326513193003261 1172215743497442447376223)
                      ·
                        rfl

theorem cell23_2282882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_2282882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282882 prefixEnd_2282882 := by exact prefixLift 2282882
  have htrace : WordTrace (prefixWord ++ tailWord_2282882) baseStart_2282882 baseEnd_2282882 := by
    simpa [prefixWord, tailWord_2282882, baseEnd_2282882] using wordTrace_append hprefix tailTrace_2282882
  have hstable : (prefixWord ++ tailWord_2282882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282882).length < 2 ^ (prefixWord ++ tailWord_2282882).sum := by decide
  have hdescent : baseEnd_2282882 < baseStart_2282882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282956 : List Nat := [2, 2, 1, 4, 2, 3, 1, 2, 2, 2, 2]
def baseStart_2282956 : Nat := 118140960795 + 2282956 * 2 ^ 59
def prefixEnd_2282956 : Nat := 4983230072969 + 3 ^ 40 * 2282956 * 2
def baseEnd_2282956 : Nat := 1172253741065875157850883

theorem tailTrace_2282956 : CollatzResearch.WordTrace tailWord_2282956 prefixEnd_2282956 1172253741065875157850883 := by
  unfold tailWord_2282956
  simp only [CollatzResearch.WordTrace]
  refine ⟨41633122958623892344278361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55510830611498523125704481 41633122958623892344278361)
  ·
    refine ⟨31224842218967919258208771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41633122958623892344278361 31224842218967919258208771)
    ·
      refine ⟨46837263328451878887313157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31224842218967919258208771 46837263328451878887313157)
      ·
        refine ⟨8781986874084727291371217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46837263328451878887313157 8781986874084727291371217)
        ·
          refine ⟨6586490155563545468528413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8781986874084727291371217 6586490155563545468528413)
          ·
            refine ⟨2469933808336329550698155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6586490155563545468528413 2469933808336329550698155)
            ·
              refine ⟨3704900712504494326047233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469933808336329550698155 3704900712504494326047233)
              ·
                refine ⟨2778675534378370744535425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3704900712504494326047233 2778675534378370744535425)
                ·
                  refine ⟨2084006650783778058401569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2778675534378370744535425 2084006650783778058401569)
                  ·
                    refine ⟨1563004988087833543801177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2084006650783778058401569 1563004988087833543801177)
                    ·
                      refine ⟨1172253741065875157850883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1563004988087833543801177 1172253741065875157850883)
                      ·
                        rfl

theorem cell23_2282956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_2282956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282956 prefixEnd_2282956 := by exact prefixLift 2282956
  have htrace : WordTrace (prefixWord ++ tailWord_2282956) baseStart_2282956 baseEnd_2282956 := by
    simpa [prefixWord, tailWord_2282956, baseEnd_2282956] using wordTrace_append hprefix tailTrace_2282956
  have hstable : (prefixWord ++ tailWord_2282956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282956).length < 2 ^ (prefixWord ++ tailWord_2282956).sum := by decide
  have hdescent : baseEnd_2282956 < baseStart_2282956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282968 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 1, 2, 5]
def baseStart_2282968 : Nat := 118140960795 + 2282968 * 2 ^ 59
def prefixEnd_2282968 : Nat := 4983230072969 + 3 ^ 40 * 2282968 * 2
def baseEnd_2282968 : Nat := 1172259902833729110900827

theorem tailTrace_2282968 : CollatzResearch.WordTrace tailWord_2282968 prefixEnd_2282968 1172259902833729110900827 := by
  unfold tailWord_2282968
  simp only [CollatzResearch.WordTrace]
  refine ⟨41633341796602155368996779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55511122395469540491995705 41633341796602155368996779)
  ·
    refine ⟨62450012694903233053495169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41633341796602155368996779 62450012694903233053495169)
    ·
      refine ⟨46837509521177424790121377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62450012694903233053495169 46837509521177424790121377)
      ·
        refine ⟨35128132140883068592591033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46837509521177424790121377 35128132140883068592591033)
        ·
          refine ⟨26346099105662301444443275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35128132140883068592591033 26346099105662301444443275)
          ·
            refine ⟨39519148658493452166664913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26346099105662301444443275 39519148658493452166664913)
            ·
              refine ⟨29639361493870089124998685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39519148658493452166664913 29639361493870089124998685)
              ·
                refine ⟨11114760560201283421874507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29639361493870089124998685 11114760560201283421874507)
                ·
                  refine ⟨16672140840301925132811761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11114760560201283421874507 16672140840301925132811761)
                  ·
                    refine ⟨12504105630226443849608821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16672140840301925132811761 12504105630226443849608821)
                    ·
                      refine ⟨1172259902833729110900827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12504105630226443849608821 1172259902833729110900827)
                      ·
                        rfl

theorem cell23_2282968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_2282968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282968 prefixEnd_2282968 := by exact prefixLift 2282968
  have htrace : WordTrace (prefixWord ++ tailWord_2282968) baseStart_2282968 baseEnd_2282968 := by
    simpa [prefixWord, tailWord_2282968, baseEnd_2282968] using wordTrace_append hprefix tailTrace_2282968
  have hstable : (prefixWord ++ tailWord_2282968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282968).length < 2 ^ (prefixWord ++ tailWord_2282968).sum := by decide
  have hdescent : baseEnd_2282968 < baseStart_2282968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282995 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 4, 4, 2]
def baseStart_2282995 : Nat := 118140960795 + 2282995 * 2 ^ 59
def prefixEnd_2282995 : Nat := 4983230072969 + 3 ^ 40 * 2282995 * 2
def baseEnd_2282995 : Nat := 1172273766811400505263203

theorem tailTrace_2282995 : CollatzResearch.WordTrace tailWord_2282995 prefixEnd_2282995 1172273766811400505263203 := by
  unfold tailWord_2282995
  simp only [CollatzResearch.WordTrace]
  refine ⟨83267668364106494349226439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55511778909404329566150959 83267668364106494349226439)
  ·
    refine ⟨124901502546159741523839659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83267668364106494349226439 124901502546159741523839659)
    ·
      refine ⟨187352253819239612285759489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124901502546159741523839659 187352253819239612285759489)
      ·
        refine ⟨140514190364429709214319617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187352253819239612285759489 140514190364429709214319617)
        ·
          refine ⟨105385642773322281910739713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140514190364429709214319617 105385642773322281910739713)
          ·
            refine ⟨79039232079991711433054785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105385642773322281910739713 79039232079991711433054785)
            ·
              refine ⟨59279424059993783574791089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79039232079991711433054785 59279424059993783574791089)
              ·
                refine ⟨44459568044995337681093317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59279424059993783574791089 44459568044995337681093317)
                ·
                  refine ⟨8336169008436625815204997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44459568044995337681093317 8336169008436625815204997)
                  ·
                    refine ⟨1563031689081867340350937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8336169008436625815204997 1563031689081867340350937)
                    ·
                      refine ⟨1172273766811400505263203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1563031689081867340350937 1172273766811400505263203)
                      ·
                        rfl

theorem cell23_2282995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 4, 2].length) (baseStart_2282995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2282995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2282995 prefixEnd_2282995 := by exact prefixLift 2282995
  have htrace : WordTrace (prefixWord ++ tailWord_2282995) baseStart_2282995 baseEnd_2282995 := by
    simpa [prefixWord, tailWord_2282995, baseEnd_2282995] using wordTrace_append hprefix tailTrace_2282995
  have hstable : (prefixWord ++ tailWord_2282995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282995).length < 2 ^ (prefixWord ++ tailWord_2282995).sum := by decide
  have hdescent : baseEnd_2282995 < baseStart_2282995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283095 : List Nat := [1, 1, 3, 2, 2, 3, 1, 3, 1, 6]
def baseStart_2283095 : Nat := 118140960795 + 2283095 * 2 ^ 59
def prefixEnd_2283095 : Nat := 4983230072969 + 3 ^ 40 * 2283095 * 2
def baseEnd_2283095 : Nat := 390775038292283371337581

theorem tailTrace_2283095 : CollatzResearch.WordTrace tailWord_2283095 prefixEnd_2283095 390775038292283371337581 := by
  unfold tailWord_2283095
  simp only [CollatzResearch.WordTrace]
  refine ⟨83271315663744211427866739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55514210442496140951911159 83271315663744211427866739)
  ·
    refine ⟨124906973495616317141800109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83271315663744211427866739 124906973495616317141800109)
    ·
      refine ⟨46840115060856118928175041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124906973495616317141800109 46840115060856118928175041)
      ·
        refine ⟨35130086295642089196131281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46840115060856118928175041 35130086295642089196131281)
        ·
          refine ⟨26347564721731566897098461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35130086295642089196131281 26347564721731566897098461)
          ·
            refine ⟨9880336770649337586411923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26347564721731566897098461 9880336770649337586411923)
            ·
              refine ⟨14820505155974006379617885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9880336770649337586411923 14820505155974006379617885)
              ·
                refine ⟨5557689433490252392356707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14820505155974006379617885 5557689433490252392356707)
                ·
                  refine ⟨8336534150235378588535061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5557689433490252392356707 8336534150235378588535061)
                  ·
                    refine ⟨390775038292283371337581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8336534150235378588535061 390775038292283371337581)
                    ·
                      rfl

theorem cell23_2283095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_2283095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283095 prefixEnd_2283095 := by exact prefixLift 2283095
  have htrace : WordTrace (prefixWord ++ tailWord_2283095) baseStart_2283095 baseEnd_2283095 := by
    simpa [prefixWord, tailWord_2283095, baseEnd_2283095] using wordTrace_append hprefix tailTrace_2283095
  have hstable : (prefixWord ++ tailWord_2283095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283095).length < 2 ^ (prefixWord ++ tailWord_2283095).sum := by decide
  have hdescent : baseEnd_2283095 < baseStart_2283095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283112 : List Nat := [2, 1, 4, 3, 1, 1, 2, 2, 1, 6]
def baseStart_2283112 : Nat := 118140960795 + 2283112 * 2 ^ 59
def prefixEnd_2283112 : Nat := 4983230072969 + 3 ^ 40 * 2283112 * 2
def baseEnd_2283112 : Nat := 390777948015992182500055

theorem tailTrace_2283112 : CollatzResearch.WordTrace tailWord_2283112 prefixEnd_2283112 390777948015992182500055 := by
  unfold tailWord_2283112
  simp only [CollatzResearch.WordTrace]
  refine ⟨41635967852341311665617795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55514623803121748887490393 41635967852341311665617795)
  ·
    refine ⟨62453951778511967498426693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41635967852341311665617795 62453951778511967498426693)
    ·
      refine ⟨11710115958470993905955005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62453951778511967498426693 11710115958470993905955005)
      ·
        refine ⟨4391293484426622714733127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11710115958470993905955005 4391293484426622714733127)
        ·
          refine ⟨6586940226639934072099691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4391293484426622714733127 6586940226639934072099691)
          ·
            refine ⟨9880410339959901108149537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6586940226639934072099691 9880410339959901108149537)
            ·
              refine ⟨7410307754969925831112153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9880410339959901108149537 7410307754969925831112153)
              ·
                refine ⟨5557730816227444373334115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7410307754969925831112153 5557730816227444373334115)
                ·
                  refine ⟨8336596224341166560001173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5557730816227444373334115 8336596224341166560001173)
                  ·
                    refine ⟨390777948015992182500055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8336596224341166560001173 390777948015992182500055)
                    ·
                      rfl

theorem cell23_2283112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_2283112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283112 prefixEnd_2283112 := by exact prefixLift 2283112
  have htrace : WordTrace (prefixWord ++ tailWord_2283112) baseStart_2283112 baseEnd_2283112 := by
    simpa [prefixWord, tailWord_2283112, baseEnd_2283112] using wordTrace_append hprefix tailTrace_2283112
  have hstable : (prefixWord ++ tailWord_2283112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283112).length < 2 ^ (prefixWord ++ tailWord_2283112).sum := by decide
  have hdescent : baseEnd_2283112 < baseStart_2283112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283136 : List Nat := [2, 1, 1, 2, 1, 4, 1, 6, 1, 2, 2]
def baseStart_2283136 : Nat := 118140960795 + 2283136 * 2 ^ 59
def prefixEnd_2283136 : Nat := 4983230072969 + 3 ^ 40 * 2283136 * 2
def baseEnd_2283136 : Nat := 1172346167583684453600055

theorem tailTrace_2283136 : CollatzResearch.WordTrace tailWord_2283136 prefixEnd_2283136 1172346167583684453600055 := by
  unfold tailWord_2283136
  simp only [CollatzResearch.WordTrace]
  refine ⟨41636405528297837715054631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55515207371063783620072841 41636405528297837715054631)
  ·
    refine ⟨62454608292446756572581947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41636405528297837715054631 62454608292446756572581947)
    ·
      refine ⟨93681912438670134858872921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62454608292446756572581947 93681912438670134858872921)
      ·
        refine ⟨70261434329002601144154691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93681912438670134858872921 70261434329002601144154691)
        ·
          refine ⟨105392151493503901716232037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70261434329002601144154691 105392151493503901716232037)
          ·
            refine ⟨19761028405031981571793507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105392151493503901716232037 19761028405031981571793507)
            ·
              refine ⟨29641542607547972357690261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19761028405031981571793507 29641542607547972357690261)
              ·
                refine ⟨1389447309728811204266731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29641542607547972357690261 1389447309728811204266731)
                ·
                  refine ⟨2084170964593216806400097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1389447309728811204266731 2084170964593216806400097)
                  ·
                    refine ⟨1563128223444912604800073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2084170964593216806400097 1563128223444912604800073)
                    ·
                      refine ⟨1172346167583684453600055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1563128223444912604800073 1172346167583684453600055)
                      ·
                        rfl

theorem cell23_2283136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 1, 2, 2].length) (baseStart_2283136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283136 prefixEnd_2283136 := by exact prefixLift 2283136
  have htrace : WordTrace (prefixWord ++ tailWord_2283136) baseStart_2283136 baseEnd_2283136 := by
    simpa [prefixWord, tailWord_2283136, baseEnd_2283136] using wordTrace_append hprefix tailTrace_2283136
  have hstable : (prefixWord ++ tailWord_2283136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283136).length < 2 ^ (prefixWord ++ tailWord_2283136).sum := by decide
  have hdescent : baseEnd_2283136 < baseStart_2283136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283146 : List Nat := [3, 1, 2, 3, 2, 2, 3, 1, 2, 4]
def baseStart_2283146 : Nat := 118140960795 + 2283146 * 2 ^ 59
def prefixEnd_2283146 : Nat := 4983230072969 + 3 ^ 40 * 2283146 * 2
def baseEnd_2283146 : Nat := 390783767463409804825003

theorem tailTrace_2283146 : CollatzResearch.WordTrace tailWord_2283146 prefixEnd_2283146 390783767463409804825003 := by
  unfold tailWord_2283146
  simp only [CollatzResearch.WordTrace]
  refine ⟨20818293946639861784493323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55515450524372964758648861 20818293946639861784493323)
  ·
    refine ⟨31227440919959792676739985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20818293946639861784493323 31227440919959792676739985)
    ·
      refine ⟨23420580689969844507554989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31227440919959792676739985 23420580689969844507554989)
      ·
        refine ⟨8782717758738691690333121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23420580689969844507554989 8782717758738691690333121)
        ·
          refine ⟨6587038319054018767749841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8782717758738691690333121 6587038319054018767749841)
          ·
            refine ⟨4940278739290514075812381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6587038319054018767749841 4940278739290514075812381)
            ·
              refine ⟨1852604527233942778429643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4940278739290514075812381 1852604527233942778429643)
              ·
                refine ⟨2778906790850914167644465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1852604527233942778429643 2778906790850914167644465)
                ·
                  refine ⟨2084180093138185625733349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2778906790850914167644465 2084180093138185625733349)
                  ·
                    refine ⟨390783767463409804825003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2084180093138185625733349 390783767463409804825003)
                    ·
                      rfl

theorem cell23_2283146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_2283146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283146 prefixEnd_2283146 := by exact prefixLift 2283146
  have htrace : WordTrace (prefixWord ++ tailWord_2283146) baseStart_2283146 baseEnd_2283146 := by
    simpa [prefixWord, tailWord_2283146, baseEnd_2283146] using wordTrace_append hprefix tailTrace_2283146
  have hstable : (prefixWord ++ tailWord_2283146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283146).length < 2 ^ (prefixWord ++ tailWord_2283146).sum := by decide
  have hdescent : baseEnd_2283146 < baseStart_2283146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283169 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 4, 1, 3]
def baseStart_2283169 : Nat := 118140960795 + 2283169 * 2 ^ 59
def prefixEnd_2283169 : Nat := 4983230072969 + 3 ^ 40 * 2283169 * 2
def baseEnd_2283169 : Nat := 1172363112445282824487403

theorem tailTrace_2283169 : CollatzResearch.WordTrace tailWord_2283169 prefixEnd_2283169 1172363112445282824487403 := by
  unfold tailWord_2283169
  simp only [CollatzResearch.WordTrace]
  refine ⟨83274014665476122066060561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55516009776984081377373707 83274014665476122066060561)
  ·
    refine ⟨62455510999107091549545421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83274014665476122066060561 62455510999107091549545421)
    ·
      refine ⟨23420816624665159331079533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62455510999107091549545421 23420816624665159331079533)
      ·
        refine ⟨8782806234249434749154825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23420816624665159331079533 8782806234249434749154825)
        ·
          refine ⟨6587104675687076061866119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8782806234249434749154825 6587104675687076061866119)
          ·
            refine ⟨9880657013530614092799179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6587104675687076061866119 9880657013530614092799179)
            ·
              refine ⟨14820985520295921139198769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9880657013530614092799179 14820985520295921139198769)
              ·
                refine ⟨11115739140221940854399077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14820985520295921139198769 11115739140221940854399077)
                ·
                  refine ⟨2084201088791613910199827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11115739140221940854399077 2084201088791613910199827)
                  ·
                    refine ⟨3126301633187420865299741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2084201088791613910199827 3126301633187420865299741)
                    ·
                      refine ⟨1172363112445282824487403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3126301633187420865299741 1172363112445282824487403)
                      ·
                        rfl

theorem cell23_2283169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_2283169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283169 prefixEnd_2283169 := by exact prefixLift 2283169
  have htrace : WordTrace (prefixWord ++ tailWord_2283169) baseStart_2283169 baseEnd_2283169 := by
    simpa [prefixWord, tailWord_2283169, baseEnd_2283169] using wordTrace_append hprefix tailTrace_2283169
  have hstable : (prefixWord ++ tailWord_2283169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283169).length < 2 ^ (prefixWord ++ tailWord_2283169).sum := by decide
  have hdescent : baseEnd_2283169 < baseStart_2283169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283176 : List Nat := [2, 1, 7, 1, 1, 2, 9]
def baseStart_2283176 : Nat := 118140960795 + 2283176 * 2 ^ 59
def prefixEnd_2283176 : Nat := 4983230072969 + 3 ^ 40 * 2283176 * 2
def baseEnd_2283176 : Nat := 14473663047035361692591

theorem tailTrace_2283176 : CollatzResearch.WordTrace tailWord_2283176 prefixEnd_2283176 14473663047035361692591 := by
  unfold tailWord_2283176
  simp only [CollatzResearch.WordTrace]
  refine ⟨41637134988225381130782691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55516179984300508174376921 41637134988225381130782691)
  ·
    refine ⟨62455702482338071696174037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41637134988225381130782691 62455702482338071696174037)
    ·
      refine ⟨1463805526929798555379079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 62455702482338071696174037 1463805526929798555379079)
      ·
        refine ⟨2195708290394697833068619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1463805526929798555379079 2195708290394697833068619)
        ·
          refine ⟨3293562435592046749602929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2195708290394697833068619 3293562435592046749602929)
          ·
            refine ⟨2470171826694035062202197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3293562435592046749602929 2470171826694035062202197)
            ·
              refine ⟨14473663047035361692591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2470171826694035062202197 14473663047035361692591)
              ·
                rfl

theorem cell23_2283176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 9].length) (baseStart_2283176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283176 prefixEnd_2283176 := by exact prefixLift 2283176
  have htrace : WordTrace (prefixWord ++ tailWord_2283176) baseStart_2283176 baseEnd_2283176 := by
    simpa [prefixWord, tailWord_2283176, baseEnd_2283176] using wordTrace_append hprefix tailTrace_2283176
  have hstable : (prefixWord ++ tailWord_2283176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283176).length < 2 ^ (prefixWord ++ tailWord_2283176).sum := by decide
  have hdescent : baseEnd_2283176 < baseStart_2283176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283213 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_2283213 : Nat := 118140960795 + 2283213 * 2 ^ 59
def prefixEnd_2283213 : Nat := 4983230072969 + 3 ^ 40 * 2283213 * 2
def baseEnd_2283213 : Nat := 1172385705594080652337201

theorem tailTrace_2283213 : CollatzResearch.WordTrace tailWord_2283213 prefixEnd_2283213 1172385705594080652337201 := by
  unfold tailWord_2283213
  simp only [CollatzResearch.WordTrace]
  refine ⟨83275619477316717580662293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55517079651544478387108195 83275619477316717580662293)
  ·
    refine ⟨3903544662999221136593545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 83275619477316717580662293 3903544662999221136593545)
    ·
      refine ⟨2927658497249415852445159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3903544662999221136593545 2927658497249415852445159)
      ·
        refine ⟨4391487745874123778667739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2927658497249415852445159 4391487745874123778667739)
        ·
          refine ⟨6587231618811185668001609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4391487745874123778667739 6587231618811185668001609)
          ·
            refine ⟨4940423714108389251001207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6587231618811185668001609 4940423714108389251001207)
            ·
              refine ⟨7410635571162583876501811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4940423714108389251001207 7410635571162583876501811)
              ·
                refine ⟨11115953356743875814752717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7410635571162583876501811 11115953356743875814752717)
                ·
                  refine ⟨4168482508778953430532269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11115953356743875814752717 4168482508778953430532269)
                  ·
                    refine ⟨1563180940792107536449601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4168482508778953430532269 1563180940792107536449601)
                    ·
                      refine ⟨1172385705594080652337201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1563180940792107536449601 1172385705594080652337201)
                      ·
                        rfl

theorem cell23_2283213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_2283213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283213 prefixEnd_2283213 := by exact prefixLift 2283213
  have htrace : WordTrace (prefixWord ++ tailWord_2283213) baseStart_2283213 baseEnd_2283213 := by
    simpa [prefixWord, tailWord_2283213, baseEnd_2283213] using wordTrace_append hprefix tailTrace_2283213
  have hstable : (prefixWord ++ tailWord_2283213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283213).length < 2 ^ (prefixWord ++ tailWord_2283213).sum := by decide
  have hdescent : baseEnd_2283213 < baseStart_2283213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283215 : List Nat := [1, 1, 2, 1, 1, 3, 1, 6, 7]
def baseStart_2283215 : Nat := 118140960795 + 2283215 * 2 ^ 59
def prefixEnd_2283215 : Nat := 4983230072969 + 3 ^ 40 * 2283215 * 2
def baseEnd_2283215 : Nat := 130265192506154404945799

theorem tailTrace_2283215 : CollatzResearch.WordTrace tailWord_2283215 prefixEnd_2283215 130265192506154404945799 := by
  unfold tailWord_2283215
  simp only [CollatzResearch.WordTrace]
  refine ⟨83275692423309471922235099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55517128282206314614823399 83275692423309471922235099)
  ·
    refine ⟨124913538634964207883352649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83275692423309471922235099 124913538634964207883352649)
    ·
      refine ⟨93685153976223155912514487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124913538634964207883352649 93685153976223155912514487)
      ·
        refine ⟨140527730964334733868771731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93685153976223155912514487 140527730964334733868771731)
        ·
          refine ⟨210791596446502100803157597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140527730964334733868771731 210791596446502100803157597)
          ·
            refine ⟨79046848667438287801184099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210791596446502100803157597 79046848667438287801184099)
            ·
              refine ⟨118570273001157431701776149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79046848667438287801184099 118570273001157431701776149)
              ·
                refine ⟨5557981546929254611020757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 118570273001157431701776149 5557981546929254611020757)
                ·
                  refine ⟨130265192506154404945799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5557981546929254611020757 130265192506154404945799)
                  ·
                    rfl

theorem cell23_2283215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 7].length) (baseStart_2283215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283215 prefixEnd_2283215 := by exact prefixLift 2283215
  have htrace : WordTrace (prefixWord ++ tailWord_2283215) baseStart_2283215 baseEnd_2283215 := by
    simpa [prefixWord, tailWord_2283215, baseEnd_2283215] using wordTrace_append hprefix tailTrace_2283215
  have hstable : (prefixWord ++ tailWord_2283215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283215).length < 2 ^ (prefixWord ++ tailWord_2283215).sum := by decide
  have hdescent : baseEnd_2283215 < baseStart_2283215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283249 : List Nat := [1, 2, 2, 2, 2, 4, 1, 4, 5]
def baseStart_2283249 : Nat := 118140960795 + 2283249 * 2 ^ 59
def prefixEnd_2283249 : Nat := 4983230072969 + 3 ^ 40 * 2283249 * 2
def baseEnd_2283249 : Nat := 130267132321960279054115

theorem tailTrace_2283249 : CollatzResearch.WordTrace tailWord_2283249 prefixEnd_2283249 130267132321960279054115 := by
  unfold tailWord_2283249
  simp only [CollatzResearch.WordTrace]
  refine ⟨83276932505186295728972801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55517955003457530485981867 83276932505186295728972801)
  ·
    refine ⟨62457699378889721796729601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83276932505186295728972801 62457699378889721796729601)
    ·
      refine ⟨46843274534167291347547201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62457699378889721796729601 46843274534167291347547201)
      ·
        refine ⟨35132455900625468510660401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46843274534167291347547201 35132455900625468510660401)
        ·
          refine ⟨26349341925469101382995301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35132455900625468510660401 26349341925469101382995301)
          ·
            refine ⟨4940501611025456509311619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26349341925469101382995301 4940501611025456509311619)
            ·
              refine ⟨7410752416538184763967429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4940501611025456509311619 7410752416538184763967429)
              ·
                refine ⟨1389516078100909643243893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7410752416538184763967429 1389516078100909643243893)
                ·
                  refine ⟨130267132321960279054115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1389516078100909643243893 130267132321960279054115)
                  ·
                    rfl

theorem cell23_2283249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 5].length) (baseStart_2283249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283249 prefixEnd_2283249 := by exact prefixLift 2283249
  have htrace : WordTrace (prefixWord ++ tailWord_2283249) baseStart_2283249 baseEnd_2283249 := by
    simpa [prefixWord, tailWord_2283249, baseEnd_2283249] using wordTrace_append hprefix tailTrace_2283249
  have hstable : (prefixWord ++ tailWord_2283249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283249).length < 2 ^ (prefixWord ++ tailWord_2283249).sum := by decide
  have hdescent : baseEnd_2283249 < baseStart_2283249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283294 : List Nat := [4, 3, 2, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_2283294 : Nat := 118140960795 + 2283294 * 2 ^ 59
def prefixEnd_2283294 : Nat := 4983230072969 + 3 ^ 40 * 2283294 * 2
def baseEnd_2283294 : Nat := 1172427297527094835424329

theorem tailTrace_2283294 : CollatzResearch.WordTrace tailWord_2283294 prefixEnd_2283294 1172427297527094835424329 := by
  unfold tailWord_2283294
  simp only [CollatzResearch.WordTrace]
  refine ⟨10409821723752908551795117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55519049193348845609573957 10409821723752908551795117)
  ·
    refine ⟨3903683146407340706923169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10409821723752908551795117 3903683146407340706923169)
    ·
      refine ⟨2927762359805505530192377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3903683146407340706923169 2927762359805505530192377)
      ·
        refine ⟨2195821769854129147644283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2927762359805505530192377 2195821769854129147644283)
        ·
          refine ⟨3293732654781193721466425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2195821769854129147644283 3293732654781193721466425)
          ·
            refine ⟨2470299491085895291099819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3293732654781193721466425 2470299491085895291099819)
            ·
              refine ⟨3705449236628842936649729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2470299491085895291099819 3705449236628842936649729)
              ·
                refine ⟨2779086927471632202487297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3705449236628842936649729 2779086927471632202487297)
                ·
                  refine ⟨2084315195603724151865473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2779086927471632202487297 2084315195603724151865473)
                  ·
                    refine ⟨1563236396702793113899105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2084315195603724151865473 1563236396702793113899105)
                    ·
                      refine ⟨1172427297527094835424329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1563236396702793113899105 1172427297527094835424329)
                      ·
                        rfl

theorem cell23_2283294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_2283294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283294 prefixEnd_2283294 := by exact prefixLift 2283294
  have htrace : WordTrace (prefixWord ++ tailWord_2283294) baseStart_2283294 baseEnd_2283294 := by
    simpa [prefixWord, tailWord_2283294, baseEnd_2283294] using wordTrace_append hprefix tailTrace_2283294
  have hstable : (prefixWord ++ tailWord_2283294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283294).length < 2 ^ (prefixWord ++ tailWord_2283294).sum := by decide
  have hdescent : baseEnd_2283294 < baseStart_2283294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283299 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 2, 4, 2]
def baseStart_2283299 : Nat := 118140960795 + 2283299 * 2 ^ 59
def prefixEnd_2283299 : Nat := 4983230072969 + 3 ^ 40 * 2283299 * 2
def baseEnd_2283299 : Nat := 1172429864930367315861805

theorem tailTrace_2283299 : CollatzResearch.WordTrace tailWord_2283299 prefixEnd_2283299 1172429864930367315861805 := by
  unfold tailWord_2283299
  simp only [CollatzResearch.WordTrace]
  refine ⟨83278756155005154268292951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55519170770003436178861967 83278756155005154268292951)
  ·
    refine ⟨124918134232507731402439427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83278756155005154268292951 124918134232507731402439427)
    ·
      refine ⟨187377201348761597103659141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124918134232507731402439427 187377201348761597103659141)
      ·
        refine ⟨35133225252892799456936089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187377201348761597103659141 35133225252892799456936089)
        ·
          refine ⟨26349918939669599592702067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35133225252892799456936089 26349918939669599592702067)
          ·
            refine ⟨39524878409504399389053101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26349918939669599592702067 39524878409504399389053101)
            ·
              refine ⟨14821829403564149770894913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39524878409504399389053101 14821829403564149770894913)
              ·
                refine ⟨11116372052673112328171185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14821829403564149770894913 11116372052673112328171185)
                ·
                  refine ⟨8337279039504834246128389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11116372052673112328171185 8337279039504834246128389)
                  ·
                    refine ⟨1563239819907156421149073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8337279039504834246128389 1563239819907156421149073)
                    ·
                      refine ⟨1172429864930367315861805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1563239819907156421149073 1172429864930367315861805)
                      ·
                        rfl

theorem cell23_2283299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_2283299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283299 prefixEnd_2283299 := by exact prefixLift 2283299
  have htrace : WordTrace (prefixWord ++ tailWord_2283299) baseStart_2283299 baseEnd_2283299 := by
    simpa [prefixWord, tailWord_2283299, baseEnd_2283299] using wordTrace_append hprefix tailTrace_2283299
  have hstable : (prefixWord ++ tailWord_2283299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283299).length < 2 ^ (prefixWord ++ tailWord_2283299).sum := by decide
  have hdescent : baseEnd_2283299 < baseStart_2283299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283326 : List Nat := [4, 2, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_2283326 : Nat := 118140960795 + 2283326 * 2 ^ 59
def prefixEnd_2283326 : Nat := 4983230072969 + 3 ^ 40 * 2283326 * 2
def baseEnd_2283326 : Nat := 390814576302679570074727

theorem tailTrace_2283326 : CollatzResearch.WordTrace tailWord_2283326 prefixEnd_2283326 390814576302679570074727 := by
  unfold tailWord_2283326
  simp only [CollatzResearch.WordTrace]
  refine ⟨10409967615738417234940729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55519827283938225253017221 10409967615738417234940729)
  ·
    refine ⟨7807475711803812926205547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10409967615738417234940729 7807475711803812926205547)
    ·
      refine ⟨11711213567705719389308321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7807475711803812926205547 11711213567705719389308321)
      ·
        refine ⟨8783410175779289541981241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11711213567705719389308321 8783410175779289541981241)
        ·
          refine ⟨6587557631834467156485931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8783410175779289541981241 6587557631834467156485931)
          ·
            refine ⟨9881336447751700734728897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6587557631834467156485931 9881336447751700734728897)
            ·
              refine ⟨7411002335813775551046673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9881336447751700734728897 7411002335813775551046673)
              ·
                refine ⟨5558251751860331663285005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7411002335813775551046673 5558251751860331663285005)
                ·
                  refine ⟨2084344406947624373731877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5558251751860331663285005 2084344406947624373731877)
                  ·
                    refine ⟨390814576302679570074727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2084344406947624373731877 390814576302679570074727)
                    ·
                      rfl

theorem cell23_2283326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_2283326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283326 prefixEnd_2283326 := by exact prefixLift 2283326
  have htrace : WordTrace (prefixWord ++ tailWord_2283326) baseStart_2283326 baseEnd_2283326 := by
    simpa [prefixWord, tailWord_2283326, baseEnd_2283326] using wordTrace_append hprefix tailTrace_2283326
  have hstable : (prefixWord ++ tailWord_2283326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283326).length < 2 ^ (prefixWord ++ tailWord_2283326).sum := by decide
  have hdescent : baseEnd_2283326 < baseStart_2283326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283352 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 7, 5]
def baseStart_2283352 : Nat := 118140960795 + 2283352 * 2 ^ 59
def prefixEnd_2283352 : Nat := 4983230072969 + 3 ^ 40 * 2283352 * 2
def baseEnd_2283352 : Nat := 390819026468351869499687

theorem tailTrace_2283352 : CollatzResearch.WordTrace tailWord_2283352 prefixEnd_2283352 390819026468351869499687 := by
  unfold tailWord_2283352
  simp only [CollatzResearch.WordTrace]
  refine ⟨41640344611906572159986155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55520459482542096213314873 41640344611906572159986155)
  ·
    refine ⟨62460516917859858239979233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41640344611906572159986155 62460516917859858239979233)
    ·
      refine ⟨46845387688394893679984425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62460516917859858239979233 46845387688394893679984425)
      ·
        refine ⟨35134040766296170259988319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46845387688394893679984425 35134040766296170259988319)
        ·
          refine ⟨52701061149444255389982479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35134040766296170259988319 52701061149444255389982479)
          ·
            refine ⟨79051591724166383084973719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52701061149444255389982479 79051591724166383084973719)
            ·
              refine ⟨118577387586249574627460579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79051591724166383084973719 118577387586249574627460579)
              ·
                refine ⟨177866081379374361941190869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118577387586249574627460579 177866081379374361941190869)
                ·
                  refine ⟨4168736282329086607996661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 177866081379374361941190869 4168736282329086607996661)
                  ·
                    refine ⟨390819026468351869499687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4168736282329086607996661 390819026468351869499687)
                    ·
                      rfl

theorem cell23_2283352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_2283352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283352 prefixEnd_2283352 := by exact prefixLift 2283352
  have htrace : WordTrace (prefixWord ++ tailWord_2283352) baseStart_2283352 baseEnd_2283352 := by
    simpa [prefixWord, tailWord_2283352, baseEnd_2283352] using wordTrace_append hprefix tailTrace_2283352
  have hstable : (prefixWord ++ tailWord_2283352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283352).length < 2 ^ (prefixWord ++ tailWord_2283352).sum := by decide
  have hdescent : baseEnd_2283352 < baseStart_2283352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283409 : List Nat := [1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 5]
def baseStart_2283409 : Nat := 118140960795 + 2283409 * 2 ^ 59
def prefixEnd_2283409 : Nat := 4983230072969 + 3 ^ 40 * 2283409 * 2
def baseEnd_2283409 : Nat := 1172486347802361885486299

theorem tailTrace_2283409 : CollatzResearch.WordTrace tailWord_2283409 prefixEnd_2283409 1172486347802361885486299 := by
  unfold tailWord_2283409
  simp only [CollatzResearch.WordTrace]
  refine ⟨83282768184606643054797281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55521845456404428703198187 83282768184606643054797281)
  ·
    refine ⟨62462076138454982291097961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83282768184606643054797281 62462076138454982291097961)
    ·
      refine ⟨46846557103841236718323471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62462076138454982291097961 46846557103841236718323471)
      ·
        refine ⟨70269835655761855077485207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46846557103841236718323471 70269835655761855077485207)
        ·
          refine ⟨105404753483642782616227811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70269835655761855077485207 105404753483642782616227811)
          ·
            refine ⟨158107130225464173924341717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105404753483642782616227811 158107130225464173924341717)
            ·
              refine ⟨3705635864659316576351759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 158107130225464173924341717 3705635864659316576351759)
              ·
                refine ⟨5558453796988974864527639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3705635864659316576351759 5558453796988974864527639)
                ·
                  refine ⟨8337680695483462296791459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5558453796988974864527639 8337680695483462296791459)
                  ·
                    refine ⟨12506521043225193445187189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8337680695483462296791459 12506521043225193445187189)
                    ·
                      refine ⟨1172486347802361885486299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12506521043225193445187189 1172486347802361885486299)
                      ·
                        rfl

theorem cell23_2283409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_2283409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283409 prefixEnd_2283409 := by exact prefixLift 2283409
  have htrace : WordTrace (prefixWord ++ tailWord_2283409) baseStart_2283409 baseEnd_2283409 := by
    simpa [prefixWord, tailWord_2283409, baseEnd_2283409] using wordTrace_append hprefix tailTrace_2283409
  have hstable : (prefixWord ++ tailWord_2283409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283409).length < 2 ^ (prefixWord ++ tailWord_2283409).sum := by decide
  have hdescent : baseEnd_2283409 < baseStart_2283409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283444 : List Nat := [2, 5, 2, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_2283444 : Nat := 118140960795 + 2283444 * 2 ^ 59
def prefixEnd_2283444 : Nat := 4983230072969 + 3 ^ 40 * 2283444 * 2
def baseEnd_2283444 : Nat := 1172504319625269248548639

theorem tailTrace_2283444 : CollatzResearch.WordTrace tailWord_2283444 prefixEnd_2283444 1172504319625269248548639 := by
  unfold tailWord_2283444
  simp only [CollatzResearch.WordTrace]
  refine ⟨41642022369739922016160693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55522696492986562688214257 41642022369739922016160693)
  ·
    refine ⟨3903939597163117689015065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41642022369739922016160693 3903939597163117689015065)
    ·
      refine ⟨2927954697872338266761299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3903939597163117689015065 2927954697872338266761299)
      ·
        refine ⟨4391932046808507400141949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2927954697872338266761299 4391932046808507400141949)
        ·
          refine ⟨1646974517553190275053231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4391932046808507400141949 1646974517553190275053231)
          ·
            refine ⟨2470461776329785412579847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1646974517553190275053231 2470461776329785412579847)
            ·
              refine ⟨3705692664494678118869771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2470461776329785412579847 3705692664494678118869771)
              ·
                refine ⟨5558538996742017178304657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3705692664494678118869771 5558538996742017178304657)
                ·
                  refine ⟨4168904247556512883728493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5558538996742017178304657 4168904247556512883728493)
                  ·
                    refine ⟨1563339092833692331398185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4168904247556512883728493 1563339092833692331398185)
                    ·
                      refine ⟨1172504319625269248548639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1563339092833692331398185 1172504319625269248548639)
                      ·
                        rfl

theorem cell23_2283444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_2283444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283444 prefixEnd_2283444 := by exact prefixLift 2283444
  have htrace : WordTrace (prefixWord ++ tailWord_2283444) baseStart_2283444 baseEnd_2283444 := by
    simpa [prefixWord, tailWord_2283444, baseEnd_2283444] using wordTrace_append hprefix tailTrace_2283444
  have hstable : (prefixWord ++ tailWord_2283444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283444).length < 2 ^ (prefixWord ++ tailWord_2283444).sum := by decide
  have hdescent : baseEnd_2283444 < baseStart_2283444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283456 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 4, 1, 3]
def baseStart_2283456 : Nat := 118140960795 + 2283456 * 2 ^ 59
def prefixEnd_2283456 : Nat := 4983230072969 + 3 ^ 40 * 2283456 * 2
def baseEnd_2283456 : Nat := 1172510481393123201598583

theorem tailTrace_2283456 : CollatzResearch.WordTrace tailWord_2283456 prefixEnd_2283456 1172510481393123201598583 := by
  unfold tailWord_2283456
  simp only [CollatzResearch.WordTrace]
  refine ⟨41642241207718185040879111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55522988276957580054505481 41642241207718185040879111)
  ·
    refine ⟨62463361811577277561318667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41642241207718185040879111 62463361811577277561318667)
    ·
      refine ⟨93695042717365916341978001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62463361811577277561318667 93695042717365916341978001)
      ·
        refine ⟨70271282038024437256483501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93695042717365916341978001 70271282038024437256483501)
        ·
          refine ⟨26351730764259163971181313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70271282038024437256483501 26351730764259163971181313)
          ·
            refine ⟨19763798073194372978385985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26351730764259163971181313 19763798073194372978385985)
            ·
              refine ⟨14822848554895779733789489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19763798073194372978385985 14822848554895779733789489)
              ·
                refine ⟨11117136416171834800342117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14822848554895779733789489 11117136416171834800342117)
                ·
                  refine ⟨2084463078032219025064147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11117136416171834800342117 2084463078032219025064147)
                  ·
                    refine ⟨3126694617048328537596221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2084463078032219025064147 3126694617048328537596221)
                    ·
                      refine ⟨1172510481393123201598583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3126694617048328537596221 1172510481393123201598583)
                      ·
                        rfl

theorem cell23_2283456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 4, 1, 3].length) (baseStart_2283456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283456 prefixEnd_2283456 := by exact prefixLift 2283456
  have htrace : WordTrace (prefixWord ++ tailWord_2283456) baseStart_2283456 baseEnd_2283456 := by
    simpa [prefixWord, tailWord_2283456, baseEnd_2283456] using wordTrace_append hprefix tailTrace_2283456
  have hstable : (prefixWord ++ tailWord_2283456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283456).length < 2 ^ (prefixWord ++ tailWord_2283456).sum := by decide
  have hdescent : baseEnd_2283456 < baseStart_2283456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283484 : List Nat := [2, 2, 6, 1, 1, 1, 3, 1, 2, 4]
def baseStart_2283484 : Nat := 118140960795 + 2283484 * 2 ^ 59
def prefixEnd_2283484 : Nat := 4983230072969 + 3 ^ 40 * 2283484 * 2
def baseEnd_2283484 : Nat := 390841619617149697349485

theorem tailTrace_2283484 : CollatzResearch.WordTrace tailWord_2283484 prefixEnd_2283484 390841619617149697349485 := by
  unfold tailWord_2283484
  simp only [CollatzResearch.WordTrace]
  refine ⟨41642751829667465431888753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55523669106223287242518337 41642751829667465431888753)
  ·
    refine ⟨31232063872250599073916565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41642751829667465431888753 31232063872250599073916565)
    ·
      refine ⟨1464002994011746831589839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31232063872250599073916565 1464002994011746831589839)
      ·
        refine ⟨2196004491017620247384759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1464002994011746831589839 2196004491017620247384759)
        ·
          refine ⟨3294006736526430371077139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2196004491017620247384759 3294006736526430371077139)
          ·
            refine ⟨4941010104789645556615709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3294006736526430371077139 4941010104789645556615709)
            ·
              refine ⟨1852878789296117083730891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4941010104789645556615709 1852878789296117083730891)
              ·
                refine ⟨2779318183944175625596337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1852878789296117083730891 2779318183944175625596337)
                ·
                  refine ⟨2084488637958131719197253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2779318183944175625596337 2084488637958131719197253)
                  ·
                    refine ⟨390841619617149697349485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2084488637958131719197253 390841619617149697349485)
                    ·
                      rfl

theorem cell23_2283484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_2283484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283484 prefixEnd_2283484 := by exact prefixLift 2283484
  have htrace : WordTrace (prefixWord ++ tailWord_2283484) baseStart_2283484 baseEnd_2283484 := by
    simpa [prefixWord, tailWord_2283484, baseEnd_2283484] using wordTrace_append hprefix tailTrace_2283484
  have hstable : (prefixWord ++ tailWord_2283484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283484).length < 2 ^ (prefixWord ++ tailWord_2283484).sum := by decide
  have hdescent : baseEnd_2283484 < baseStart_2283484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283489 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 2, 6]
def baseStart_2283489 : Nat := 118140960795 + 2283489 * 2 ^ 59
def prefixEnd_2283489 : Nat := 4983230072969 + 3 ^ 40 * 2283489 * 2
def baseEnd_2283489 : Nat := 390842475418240524161977

theorem tailTrace_2283489 : CollatzResearch.WordTrace tailWord_2283489 prefixEnd_2283489 390842475418240524161977 := by
  unfold tailWord_2283489
  simp only [CollatzResearch.WordTrace]
  refine ⟨83285686024316816717709521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55523790682877877811806347 83285686024316816717709521)
  ·
    refine ⟨62464264518237612538282141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83285686024316816717709521 62464264518237612538282141)
    ·
      refine ⟨23424099194339104701855803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62464264518237612538282141 23424099194339104701855803)
      ·
        refine ⟨35136148791508657052783705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23424099194339104701855803 35136148791508657052783705)
        ·
          refine ⟨26352111593631492789587779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35136148791508657052783705 26352111593631492789587779)
          ·
            refine ⟨39528167390447239184381669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26352111593631492789587779 39528167390447239184381669)
            ·
              refine ⟨7411531385708857347071563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39528167390447239184381669 7411531385708857347071563)
              ·
                refine ⟨11117297078563286020607345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7411531385708857347071563 11117297078563286020607345)
                ·
                  refine ⟨8337972808922464515455509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11117297078563286020607345 8337972808922464515455509)
                  ·
                    refine ⟨390842475418240524161977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8337972808922464515455509 390842475418240524161977)
                    ·
                      rfl

theorem cell23_2283489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_2283489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283489 prefixEnd_2283489 := by exact prefixLift 2283489
  have htrace : WordTrace (prefixWord ++ tailWord_2283489) baseStart_2283489 baseEnd_2283489 := by
    simpa [prefixWord, tailWord_2283489, baseEnd_2283489] using wordTrace_append hprefix tailTrace_2283489
  have hstable : (prefixWord ++ tailWord_2283489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283489).length < 2 ^ (prefixWord ++ tailWord_2283489).sum := by decide
  have hdescent : baseEnd_2283489 < baseStart_2283489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283499 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 3]
def baseStart_2283499 : Nat := 118140960795 + 2283499 * 2 ^ 59
def prefixEnd_2283499 : Nat := 4983230072969 + 3 ^ 40 * 2283499 * 2
def baseEnd_2283499 : Nat := 1172532561061266533360885

theorem tailTrace_2283499 : CollatzResearch.WordTrace tailWord_2283499 prefixEnd_2283499 1172532561061266533360885 := by
  unfold tailWord_2283499
  simp only [CollatzResearch.WordTrace]
  refine ⟨83286050754280588425573551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55524033836187058950382367 83286050754280588425573551)
  ·
    refine ⟨124929076131420882638360327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83286050754280588425573551 124929076131420882638360327)
    ·
      refine ⟨187393614197131323957540491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124929076131420882638360327 187393614197131323957540491)
      ·
        refine ⟨281090421295696985936310737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187393614197131323957540491 281090421295696985936310737)
        ·
          refine ⟨210817815971772739452233053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281090421295696985936310737 210817815971772739452233053)
          ·
            refine ⟨79056680989414777294587395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210817815971772739452233053 79056680989414777294587395)
            ·
              refine ⟨118585021484122165941881093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79056680989414777294587395 118585021484122165941881093)
              ·
                refine ⟨22234691528272906114102705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118585021484122165941881093 22234691528272906114102705)
                ·
                  refine ⟨16676018646204679585577029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22234691528272906114102705 16676018646204679585577029)
                  ·
                    refine ⟨3126753496163377422295693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16676018646204679585577029 3126753496163377422295693)
                    ·
                      refine ⟨1172532561061266533360885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3126753496163377422295693 1172532561061266533360885)
                      ·
                        rfl

theorem cell23_2283499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 3].length) (baseStart_2283499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283499 prefixEnd_2283499 := by exact prefixLift 2283499
  have htrace : WordTrace (prefixWord ++ tailWord_2283499) baseStart_2283499 baseEnd_2283499 := by
    simpa [prefixWord, tailWord_2283499, baseEnd_2283499] using wordTrace_append hprefix tailTrace_2283499
  have hstable : (prefixWord ++ tailWord_2283499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283499).length < 2 ^ (prefixWord ++ tailWord_2283499).sum := by decide
  have hdescent : baseEnd_2283499 < baseStart_2283499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283513 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 4, 2, 2]
def baseStart_2283513 : Nat := 118140960795 + 2283513 * 2 ^ 59
def prefixEnd_2283513 : Nat := 4983230072969 + 3 ^ 40 * 2283513 * 2
def baseEnd_2283513 : Nat := 1172539749790429478585821

theorem tailTrace_2283513 : CollatzResearch.WordTrace tailWord_2283513 prefixEnd_2283513 1172539749790429478585821 := by
  unfold tailWord_2283513
  simp only [CollatzResearch.WordTrace]
  refine ⟨83286561376229868816583193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55524374250819912544388795 83286561376229868816583193)
  ·
    refine ⟨62464921032172401612437395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83286561376229868816583193 62464921032172401612437395)
    ·
      refine ⟨93697381548258602418656093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62464921032172401612437395 93697381548258602418656093)
      ·
        refine ⟨35136518080596975906996035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93697381548258602418656093 35136518080596975906996035)
        ·
          refine ⟨52704777120895463860494053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35136518080596975906996035 52704777120895463860494053)
          ·
            refine ⟨9882145710167899473842635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52704777120895463860494053 9882145710167899473842635)
            ·
              refine ⟨14823218565251849210763953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9882145710167899473842635 14823218565251849210763953)
              ·
                refine ⟨11117413923938886908072965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14823218565251849210763953 11117413923938886908072965)
                ·
                  refine ⟨2084515110738541295263681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11117413923938886908072965 2084515110738541295263681)
                  ·
                    refine ⟨1563386333053905971447761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2084515110738541295263681 1563386333053905971447761)
                    ·
                      refine ⟨1172539749790429478585821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1563386333053905971447761 1172539749790429478585821)
                      ·
                        rfl

theorem cell23_2283513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_2283513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283513 prefixEnd_2283513 := by exact prefixLift 2283513
  have htrace : WordTrace (prefixWord ++ tailWord_2283513) baseStart_2283513 baseEnd_2283513 := by
    simpa [prefixWord, tailWord_2283513, baseEnd_2283513] using wordTrace_append hprefix tailTrace_2283513
  have hstable : (prefixWord ++ tailWord_2283513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283513).length < 2 ^ (prefixWord ++ tailWord_2283513).sum := by decide
  have hdescent : baseEnd_2283513 < baseStart_2283513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283589 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 1, 5, 5]
def baseStart_2283589 : Nat := 118140960795 + 2283589 * 2 ^ 59
def prefixEnd_2283589 : Nat := 4983230072969 + 3 ^ 40 * 2283589 * 2
def baseEnd_2283589 : Nat := 1172578774320171181235471

theorem tailTrace_2283589 : CollatzResearch.WordTrace tailWord_2283589 prefixEnd_2283589 1172578774320171181235471 := by
  unfold tailWord_2283589
  simp only [CollatzResearch.WordTrace]
  refine ⟨83289333323954533796349821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55526222215969689197566547 83289333323954533796349821)
  ·
    refine ⟨31233499996482950173631183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83289333323954533796349821 31233499996482950173631183)
    ·
      refine ⟨46850249994724425260446775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31233499996482950173631183 46850249994724425260446775)
      ·
        refine ⟨70275374992086637890670163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46850249994724425260446775 70275374992086637890670163)
        ·
          refine ⟨105413062488129956836005245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70275374992086637890670163 105413062488129956836005245)
          ·
            refine ⟨39529898433048733813501967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105413062488129956836005245 39529898433048733813501967)
            ·
              refine ⟨59294847649573100720252951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39529898433048733813501967 59294847649573100720252951)
              ·
                refine ⟨88942271474359651080379427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59294847649573100720252951 88942271474359651080379427)
                ·
                  refine ⟨133413407211539476620569141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88942271474359651080379427 133413407211539476620569141)
                  ·
                    refine ⟨12507506926081825933178357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 133413407211539476620569141 12507506926081825933178357)
                    ·
                      refine ⟨1172578774320171181235471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12507506926081825933178357 1172578774320171181235471)
                      ·
                        rfl

theorem cell23_2283589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_2283589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283589 prefixEnd_2283589 := by exact prefixLift 2283589
  have htrace : WordTrace (prefixWord ++ tailWord_2283589) baseStart_2283589 baseEnd_2283589 := by
    simpa [prefixWord, tailWord_2283589, baseEnd_2283589] using wordTrace_append hprefix tailTrace_2283589
  have hstable : (prefixWord ++ tailWord_2283589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283589).length < 2 ^ (prefixWord ++ tailWord_2283589).sum := by decide
  have hdescent : baseEnd_2283589 < baseStart_2283589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283590 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_2283590 : Nat := 118140960795 + 2283590 * 2 ^ 59
def prefixEnd_2283590 : Nat := 4983230072969 + 3 ^ 40 * 2283590 * 2
def baseEnd_2283590 : Nat := 1172579287800825677322967

theorem tailTrace_2283590 : CollatzResearch.WordTrace tailWord_2283590 prefixEnd_2283590 1172579287800825677322967 := by
  unfold tailWord_2283590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2602792806154715967723007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55526246531300607311424149 2602792806154715967723007)
  ·
    refine ⟨3904189209232073951584511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2602792806154715967723007 3904189209232073951584511)
    ·
      refine ⟨5856283813848110927376767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3904189209232073951584511 5856283813848110927376767)
      ·
        refine ⟨8784425720772166391065151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5856283813848110927376767 8784425720772166391065151)
        ·
          refine ⟨13176638581158249586597727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8784425720772166391065151 13176638581158249586597727)
          ·
            refine ⟨19764957871737374379896591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13176638581158249586597727 19764957871737374379896591)
            ·
              refine ⟨29647436807606061569844887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19764957871737374379896591 29647436807606061569844887)
              ·
                refine ⟨44471155211409092354767331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29647436807606061569844887 44471155211409092354767331)
                ·
                  refine ⟨66706732817113638532150997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44471155211409092354767331 66706732817113638532150997)
                  ·
                    refine ⟨1563439050401100903097289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 66706732817113638532150997 1563439050401100903097289)
                    ·
                      refine ⟨1172579287800825677322967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1563439050401100903097289 1172579287800825677322967)
                      ·
                        rfl

theorem cell23_2283590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_2283590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283590 prefixEnd_2283590 := by exact prefixLift 2283590
  have htrace : WordTrace (prefixWord ++ tailWord_2283590) baseStart_2283590 baseEnd_2283590 := by
    simpa [prefixWord, tailWord_2283590, baseEnd_2283590] using wordTrace_append hprefix tailTrace_2283590
  have hstable : (prefixWord ++ tailWord_2283590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283590).length < 2 ^ (prefixWord ++ tailWord_2283590).sum := by decide
  have hdescent : baseEnd_2283590 < baseStart_2283590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283599 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 6]
def baseStart_2283599 : Nat := 118140960795 + 2283599 * 2 ^ 59
def prefixEnd_2283599 : Nat := 4983230072969 + 3 ^ 40 * 2283599 * 2
def baseEnd_2283599 : Nat := 1172583909126716142110425

theorem tailTrace_2283599 : CollatzResearch.WordTrace tailWord_2283599 prefixEnd_2283599 1172583909126716142110425 := by
  unfold tailWord_2283599
  simp only [CollatzResearch.WordTrace]
  refine ⟨83289698053918305504213851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55526465369278870336142567 83289698053918305504213851)
  ·
    refine ⟨124934547080877458256320777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83289698053918305504213851 124934547080877458256320777)
    ·
      refine ⟨93700910310658093692240583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124934547080877458256320777 93700910310658093692240583)
      ·
        refine ⟨140551365465987140538360875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93700910310658093692240583 140551365465987140538360875)
        ·
          refine ⟨210827048198980710807541313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140551365465987140538360875 210827048198980710807541313)
          ·
            refine ⟨158120286149235533105655985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210827048198980710807541313 158120286149235533105655985)
            ·
              refine ⟨118590214611926649829241989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158120286149235533105655985 118590214611926649829241989)
              ·
                refine ⟨22235665239736246842982873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118590214611926649829241989 22235665239736246842982873)
                ·
                  refine ⟨16676748929802185132237155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22235665239736246842982873 16676748929802185132237155)
                  ·
                    refine ⟨25015123394703277698355733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16676748929802185132237155 25015123394703277698355733)
                    ·
                      refine ⟨1172583909126716142110425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25015123394703277698355733 1172583909126716142110425)
                      ·
                        rfl

theorem cell23_2283599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_2283599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283599 prefixEnd_2283599 := by exact prefixLift 2283599
  have htrace : WordTrace (prefixWord ++ tailWord_2283599) baseStart_2283599 baseEnd_2283599 := by
    simpa [prefixWord, tailWord_2283599, baseEnd_2283599] using wordTrace_append hprefix tailTrace_2283599
  have hstable : (prefixWord ++ tailWord_2283599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283599).length < 2 ^ (prefixWord ++ tailWord_2283599).sum := by decide
  have hdescent : baseEnd_2283599 < baseStart_2283599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283697 : List Nat := [1, 2, 2, 5, 2, 1, 1, 2, 2, 3, 2]
def baseStart_2283697 : Nat := 118140960795 + 2283697 * 2 ^ 59
def prefixEnd_2283697 : Nat := 4983230072969 + 3 ^ 40 * 2283697 * 2
def baseEnd_2283697 : Nat := 1172634230230856758684975

theorem tailTrace_2283697 : CollatzResearch.WordTrace tailWord_2283697 prefixEnd_2283697 1172634230230856758684975 := by
  unfold tailWord_2283697
  simp only [CollatzResearch.WordTrace]
  refine ⟨83293272407563268241281345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55528848271708845494187563 83293272407563268241281345)
  ·
    refine ⟨62469954305672451180961009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83293272407563268241281345 62469954305672451180961009)
    ·
      refine ⟨46852465729254338385720757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62469954305672451180961009 46852465729254338385720757)
      ·
        refine ⟨4392418662117594223661321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46852465729254338385720757 4392418662117594223661321)
        ·
          refine ⟨3294313996588195667745991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4392418662117594223661321 3294313996588195667745991)
          ·
            refine ⟨4941470994882293501618987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3294313996588195667745991 4941470994882293501618987)
            ·
              refine ⟨7412206492323440252428481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4941470994882293501618987 7412206492323440252428481)
              ·
                refine ⟨5559154869242580189321361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7412206492323440252428481 5559154869242580189321361)
                ·
                  refine ⟨4169366151931935141991021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5559154869242580189321361 4169366151931935141991021)
                  ·
                    refine ⟨1563512306974475678246633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4169366151931935141991021 1563512306974475678246633)
                    ·
                      refine ⟨1172634230230856758684975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1563512306974475678246633 1172634230230856758684975)
                      ·
                        rfl

theorem cell23_2283697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_2283697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283697 prefixEnd_2283697 := by exact prefixLift 2283697
  have htrace : WordTrace (prefixWord ++ tailWord_2283697) baseStart_2283697 baseEnd_2283697 := by
    simpa [prefixWord, tailWord_2283697, baseEnd_2283697] using wordTrace_append hprefix tailTrace_2283697
  have hstable : (prefixWord ++ tailWord_2283697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283697).length < 2 ^ (prefixWord ++ tailWord_2283697).sum := by decide
  have hdescent : baseEnd_2283697 < baseStart_2283697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283703 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 4, 4]
def baseStart_2283703 : Nat := 118140960795 + 2283703 * 2 ^ 59
def prefixEnd_2283703 : Nat := 4983230072969 + 3 ^ 40 * 2283703 * 2
def baseEnd_2283703 : Nat := 390879103704927911736649

theorem tailTrace_2283703 : CollatzResearch.WordTrace tailWord_2283703 prefixEnd_2283703 390879103704927911736649 := by
  unfold tailWord_2283703
  simp only [CollatzResearch.WordTrace]
  refine ⟨83293491245541531265999763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55528994163694354177333175 83293491245541531265999763)
  ·
    refine ⟨124940236868312296898999645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83293491245541531265999763 124940236868312296898999645)
    ·
      refine ⟨46852588825617111337124867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124940236868312296898999645 46852588825617111337124867)
      ·
        refine ⟨70278883238425667005687301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46852588825617111337124867 70278883238425667005687301)
        ·
          refine ⟨13177290607204812563566369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70278883238425667005687301 13177290607204812563566369)
          ·
            refine ⟨9882967955403609422674777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13177290607204812563566369 9882967955403609422674777)
            ·
              refine ⟨7412225966552707067006083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9882967955403609422674777 7412225966552707067006083)
              ·
                refine ⟨11118338949829060600509125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7412225966552707067006083 11118338949829060600509125)
                ·
                  refine ⟨2084688553092948862595461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11118338949829060600509125 2084688553092948862595461)
                  ·
                    refine ⟨390879103704927911736649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2084688553092948862595461 390879103704927911736649)
                    ·
                      rfl

theorem cell23_2283703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_2283703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283703 prefixEnd_2283703 := by exact prefixLift 2283703
  have htrace : WordTrace (prefixWord ++ tailWord_2283703) baseStart_2283703 baseEnd_2283703 := by
    simpa [prefixWord, tailWord_2283703, baseEnd_2283703] using wordTrace_append hprefix tailTrace_2283703
  have hstable : (prefixWord ++ tailWord_2283703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283703).length < 2 ^ (prefixWord ++ tailWord_2283703).sum := by decide
  have hdescent : baseEnd_2283703 < baseStart_2283703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283706 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6]
def baseStart_2283706 : Nat := 118140960795 + 2283706 * 2 ^ 59
def prefixEnd_2283706 : Nat := 4983230072969 + 3 ^ 40 * 2283706 * 2
def baseEnd_2283706 : Nat := 1172638851556747223472433

theorem tailTrace_2283706 : CollatzResearch.WordTrace tailWord_2283706 prefixEnd_2283706 1172638851556747223472433 := by
  unfold tailWord_2283706
  simp only [CollatzResearch.WordTrace]
  refine ⟨20823400166132665694589743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55529067109687108518905981 20823400166132665694589743)
  ·
    refine ⟨31235100249198998541884615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20823400166132665694589743 31235100249198998541884615)
    ·
      refine ⟨46852650373798497812826923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31235100249198998541884615 46852650373798497812826923)
      ·
        refine ⟨70278975560697746719240385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46852650373798497812826923 70278975560697746719240385)
        ·
          refine ⟨52709231670523310039430289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70278975560697746719240385 52709231670523310039430289)
          ·
            refine ⟨39531923752892482529572717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52709231670523310039430289 39531923752892482529572717)
            ·
              refine ⟨14824471407334680948589769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39531923752892482529572717 14824471407334680948589769)
              ·
                refine ⟨11118353555501010711442327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14824471407334680948589769 11118353555501010711442327)
                ·
                  refine ⟨16677530333251516067163491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11118353555501010711442327 16677530333251516067163491)
                  ·
                    refine ⟨25016295499877274100745237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16677530333251516067163491 25016295499877274100745237)
                    ·
                      refine ⟨1172638851556747223472433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25016295499877274100745237 1172638851556747223472433)
                      ·
                        rfl

theorem cell23_2283706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_2283706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283706 prefixEnd_2283706 := by exact prefixLift 2283706
  have htrace : WordTrace (prefixWord ++ tailWord_2283706) baseStart_2283706 baseEnd_2283706 := by
    simpa [prefixWord, tailWord_2283706, baseEnd_2283706] using wordTrace_append hprefix tailTrace_2283706
  have hstable : (prefixWord ++ tailWord_2283706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283706).length < 2 ^ (prefixWord ++ tailWord_2283706).sum := by decide
  have hdescent : baseEnd_2283706 < baseStart_2283706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283724 : List Nat := [2, 2, 1, 6, 2, 1, 1, 2, 1, 5]
def baseStart_2283724 : Nat := 118140960795 + 2283724 * 2 ^ 59
def prefixEnd_2283724 : Nat := 4983230072969 + 3 ^ 40 * 2283724 * 2
def baseEnd_2283724 : Nat := 390882698069509384349117

theorem tailTrace_2283724 : CollatzResearch.WordTrace tailWord_2283724 prefixEnd_2283724 390882698069509384349117 := by
  unfold tailWord_2283724
  simp only [CollatzResearch.WordTrace]
  refine ⟨41647128589232725926257113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55529504785643634568342817 41647128589232725926257113)
  ·
    refine ⟨31235346441924544444692835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41647128589232725926257113 31235346441924544444692835)
    ·
      refine ⟨46853019662886816667039253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31235346441924544444692835 46853019662886816667039253)
      ·
        refine ⟨2196235296697819531267465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46853019662886816667039253 2196235296697819531267465)
        ·
          refine ⟨1647176472523364648450599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2196235296697819531267465 1647176472523364648450599)
          ·
            refine ⟨2470764708785046972675899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1647176472523364648450599 2470764708785046972675899)
            ·
              refine ⟨3706147063177570459013849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2470764708785046972675899 3706147063177570459013849)
              ·
                refine ⟨2779610297383177844260387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3706147063177570459013849 2779610297383177844260387)
                ·
                  refine ⟨4169415446074766766390581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2779610297383177844260387 4169415446074766766390581)
                  ·
                    refine ⟨390882698069509384349117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4169415446074766766390581 390882698069509384349117)
                    ·
                      rfl

theorem cell23_2283724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 1, 5].length) (baseStart_2283724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283724 prefixEnd_2283724 := by exact prefixLift 2283724
  have htrace : WordTrace (prefixWord ++ tailWord_2283724) baseStart_2283724 baseEnd_2283724 := by
    simpa [prefixWord, tailWord_2283724, baseEnd_2283724] using wordTrace_append hprefix tailTrace_2283724
  have hstable : (prefixWord ++ tailWord_2283724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283724).length < 2 ^ (prefixWord ++ tailWord_2283724).sum := by decide
  have hdescent : baseEnd_2283724 < baseStart_2283724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283730 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_2283730 : Nat := 118140960795 + 2283730 * 2 ^ 59
def prefixEnd_2283730 : Nat := 4983230072969 + 3 ^ 40 * 2283730 * 2
def baseEnd_2283730 : Nat := 1172651175092455129572323

theorem tailTrace_2283730 : CollatzResearch.WordTrace tailWord_2283730 prefixEnd_2283730 1172651175092455129572323 := by
  unfold tailWord_2283730
  simp only [CollatzResearch.WordTrace]
  refine ⟨20823619004110928719308161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55529650677629143251488429 20823619004110928719308161)
  ·
    refine ⟨15617714253083196539481121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20823619004110928719308161 15617714253083196539481121)
    ·
      refine ⟨11713285689812397404610841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15617714253083196539481121 11713285689812397404610841)
      ·
        refine ⟨8784964267359298053458131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11713285689812397404610841 8784964267359298053458131)
        ·
          refine ⟨13177446401038947080187197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8784964267359298053458131 13177446401038947080187197)
          ·
            refine ⟨4941542400389605155070199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13177446401038947080187197 4941542400389605155070199)
            ·
              refine ⟨7412313600584407732605299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4941542400389605155070199 7412313600584407732605299)
              ·
                refine ⟨11118470400876611598907949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7412313600584407732605299 11118470400876611598907949)
                ·
                  refine ⟨4169426400328729349590481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11118470400876611598907949 4169426400328729349590481)
                  ·
                    refine ⟨3127069800246547012192861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4169426400328729349590481 3127069800246547012192861)
                    ·
                      refine ⟨1172651175092455129572323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3127069800246547012192861 1172651175092455129572323)
                      ·
                        rfl

theorem cell23_2283730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_2283730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283730 prefixEnd_2283730 := by exact prefixLift 2283730
  have htrace : WordTrace (prefixWord ++ tailWord_2283730) baseStart_2283730 baseEnd_2283730 := by
    simpa [prefixWord, tailWord_2283730, baseEnd_2283730] using wordTrace_append hprefix tailTrace_2283730
  have hstable : (prefixWord ++ tailWord_2283730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283730).length < 2 ^ (prefixWord ++ tailWord_2283730).sum := by decide
  have hdescent : baseEnd_2283730 < baseStart_2283730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283747 : List Nat := [1, 1, 1, 8, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2283747 : Nat := 118140960795 + 2283747 * 2 ^ 59
def prefixEnd_2283747 : Nat := 4983230072969 + 3 ^ 40 * 2283747 * 2
def baseEnd_2283747 : Nat := 1172659904263581563059745

theorem tailTrace_2283747 : CollatzResearch.WordTrace tailWord_2283747 prefixEnd_2283747 1172659904263581563059745 := by
  unfold tailWord_2283747
  simp only [CollatzResearch.WordTrace]
  refine ⟨83295096057382126780601495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55530064038254751187067663 83295096057382126780601495)
  ·
    refine ⟨124942644086073190170902243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83295096057382126780601495 124942644086073190170902243)
    ·
      refine ⟨187413966129109785256353365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124942644086073190170902243 187413966129109785256353365)
      ·
        refine ⟨2196257415575505295972891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 187413966129109785256353365 2196257415575505295972891)
        ·
          refine ⟨3294386123363257943959337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2196257415575505295972891 3294386123363257943959337)
          ·
            refine ⟨2470789592522443457969503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3294386123363257943959337 2470789592522443457969503)
            ·
              refine ⟨3706184388783665186954255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2470789592522443457969503 3706184388783665186954255)
              ·
                refine ⟨5559276583175497780431383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3706184388783665186954255 5559276583175497780431383)
                ·
                  refine ⟨8338914874763246670647075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5559276583175497780431383 8338914874763246670647075)
                  ·
                    refine ⟨12508372312144870005970613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8338914874763246670647075 12508372312144870005970613)
                    ·
                      refine ⟨1172659904263581563059745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12508372312144870005970613 1172659904263581563059745)
                      ·
                        rfl

theorem cell23_2283747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2283747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283747 prefixEnd_2283747 := by exact prefixLift 2283747
  have htrace : WordTrace (prefixWord ++ tailWord_2283747) baseStart_2283747 baseEnd_2283747 := by
    simpa [prefixWord, tailWord_2283747, baseEnd_2283747] using wordTrace_append hprefix tailTrace_2283747
  have hstable : (prefixWord ++ tailWord_2283747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283747).length < 2 ^ (prefixWord ++ tailWord_2283747).sum := by decide
  have hdescent : baseEnd_2283747 < baseStart_2283747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283770 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2]
def baseStart_2283770 : Nat := 118140960795 + 2283770 * 2 ^ 59
def prefixEnd_2283770 : Nat := 4983230072969 + 3 ^ 40 * 2283770 * 2
def baseEnd_2283770 : Nat := 1172671714318634973072139

theorem tailTrace_2283770 : CollatzResearch.WordTrace tailWord_2283770 prefixEnd_2283770 1172671714318634973072139 := by
  unfold tailWord_2283770
  simp only [CollatzResearch.WordTrace]
  refine ⟨20823983734074700427172191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55530623290865867805792509 20823983734074700427172191)
  ·
    refine ⟨31235975601112050640758287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20823983734074700427172191 31235975601112050640758287)
    ·
      refine ⟨46853963401668075961137431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31235975601112050640758287 46853963401668075961137431)
      ·
        refine ⟨70280945102502113941706147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46853963401668075961137431 70280945102502113941706147)
        ·
          refine ⟨105421417653753170912559221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70280945102502113941706147 105421417653753170912559221)
          ·
            refine ⟨9883257905039359773052427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105421417653753170912559221 9883257905039359773052427)
            ·
              refine ⟨14824886857559039659578641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9883257905039359773052427 14824886857559039659578641)
              ·
                refine ⟨11118665143169279744683981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14824886857559039659578641 11118665143169279744683981)
                ·
                  refine ⟨4169499428688479904256493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11118665143169279744683981 4169499428688479904256493)
                  ·
                    refine ⟨1563562285758179964096185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4169499428688479904256493 1563562285758179964096185)
                    ·
                      refine ⟨1172671714318634973072139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1563562285758179964096185 1172671714318634973072139)
                      ·
                        rfl

theorem cell23_2283770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2].length) (baseStart_2283770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283770 prefixEnd_2283770 := by exact prefixLift 2283770
  have htrace : WordTrace (prefixWord ++ tailWord_2283770) baseStart_2283770 baseEnd_2283770 := by
    simpa [prefixWord, tailWord_2283770, baseEnd_2283770] using wordTrace_append hprefix tailTrace_2283770
  have hstable : (prefixWord ++ tailWord_2283770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283770).length < 2 ^ (prefixWord ++ tailWord_2283770).sum := by decide
  have hdescent : baseEnd_2283770 < baseStart_2283770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283776 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 1, 8]
def baseStart_2283776 : Nat := 118140960795 + 2283776 * 2 ^ 59
def prefixEnd_2283776 : Nat := 4983230072969 + 3 ^ 40 * 2283776 * 2
def baseEnd_2283776 : Nat := 390891598400853983199037

theorem tailTrace_2283776 : CollatzResearch.WordTrace tailWord_2283776 prefixEnd_2283776 390891598400853983199037 := by
  unfold tailWord_2283776
  simp only [CollatzResearch.WordTrace]
  refine ⟨41648076887138532366703591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55530769182851376488938121 41648076887138532366703591)
  ·
    refine ⟨62472115330707798550055387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41648076887138532366703591 62472115330707798550055387)
    ·
      refine ⟨93708172996061697825083081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62472115330707798550055387 93708172996061697825083081)
      ·
        refine ⟨70281129747046273368812311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93708172996061697825083081 70281129747046273368812311)
        ·
          refine ⟨105421694620569410053218467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70281129747046273368812311 105421694620569410053218467)
          ·
            refine ⟨158132541930854115079827701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105421694620569410053218467 158132541930854115079827701)
            ·
              refine ⟨14824925806017573288733847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 158132541930854115079827701 14824925806017573288733847)
              ·
                refine ⟨22237388709026359933100771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14824925806017573288733847 22237388709026359933100771)
                ·
                  refine ⟨33356083063539539899651157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22237388709026359933100771 33356083063539539899651157)
                  ·
                    refine ⟨390891598400853983199037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33356083063539539899651157 390891598400853983199037)
                    ·
                      rfl

theorem cell23_2283776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 1, 8].length) (baseStart_2283776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283776 prefixEnd_2283776 := by exact prefixLift 2283776
  have htrace : WordTrace (prefixWord ++ tailWord_2283776) baseStart_2283776 baseEnd_2283776 := by
    simpa [prefixWord, tailWord_2283776, baseEnd_2283776] using wordTrace_append hprefix tailTrace_2283776
  have hstable : (prefixWord ++ tailWord_2283776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283776).length < 2 ^ (prefixWord ++ tailWord_2283776).sum := by decide
  have hdescent : baseEnd_2283776 < baseStart_2283776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283800 : List Nat := [2, 1, 2, 3, 1, 2, 1, 4, 1, 4, 2]
def baseStart_2283800 : Nat := 118140960795 + 2283800 * 2 ^ 59
def prefixEnd_2283800 : Nat := 4983230072969 + 3 ^ 40 * 2283800 * 2
def baseEnd_2283800 : Nat := 1172687118738269855697001

theorem tailTrace_2283800 : CollatzResearch.WordTrace tailWord_2283800 prefixEnd_2283800 1172687118738269855697001 := by
  unfold tailWord_2283800
  simp only [CollatzResearch.WordTrace]
  refine ⟨41648514563095058416140427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55531352750793411221520569 41648514563095058416140427)
  ·
    refine ⟨62472771844642587624210641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41648514563095058416140427 62472771844642587624210641)
    ·
      refine ⟨46854578883481940718157981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62472771844642587624210641 46854578883481940718157981)
      ·
        refine ⟨17570467081305727769309243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46854578883481940718157981 17570467081305727769309243)
        ·
          refine ⟨26355700621958591653963865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17570467081305727769309243 26355700621958591653963865)
          ·
            refine ⟨19766775466468943740472899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26355700621958591653963865 19766775466468943740472899)
            ·
              refine ⟨29650163199703415610709349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19766775466468943740472899 29650163199703415610709349)
              ·
                refine ⟨5559405599944390427008003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29650163199703415610709349 5559405599944390427008003)
                ·
                  refine ⟨8339108399916585640512005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5559405599944390427008003 8339108399916585640512005)
                  ·
                    refine ⟨1563582824984359807596001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8339108399916585640512005 1563582824984359807596001)
                    ·
                      refine ⟨1172687118738269855697001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1563582824984359807596001 1172687118738269855697001)
                      ·
                        rfl

theorem cell23_2283800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_2283800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283800 prefixEnd_2283800 := by exact prefixLift 2283800
  have htrace : WordTrace (prefixWord ++ tailWord_2283800) baseStart_2283800 baseEnd_2283800 := by
    simpa [prefixWord, tailWord_2283800, baseEnd_2283800] using wordTrace_append hprefix tailTrace_2283800
  have hstable : (prefixWord ++ tailWord_2283800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283800).length < 2 ^ (prefixWord ++ tailWord_2283800).sum := by decide
  have hdescent : baseEnd_2283800 < baseStart_2283800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283857 : List Nat := [1, 2, 2, 1, 4, 4, 1, 3, 5]
def baseStart_2283857 : Nat := 118140960795 + 2283857 * 2 ^ 59
def prefixEnd_2283857 : Nat := 4983230072969 + 3 ^ 40 * 2283857 * 2
def baseEnd_2283857 : Nat := 130301820792841792520471

theorem tailTrace_2283857 : CollatzResearch.WordTrace tailWord_2283857 prefixEnd_2283857 130301820792841792520471 := by
  unfold tailWord_2283857
  simp only [CollatzResearch.WordTrace]
  refine ⟨83299108086983615567105825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55532738724655743711403883 83299108086983615567105825)
  ·
    refine ⟨62474331065237711675329369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83299108086983615567105825 62474331065237711675329369)
    ·
      refine ⟨46855748298928283756497027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62474331065237711675329369 46855748298928283756497027)
      ·
        refine ⟨70283622448392425634745541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46855748298928283756497027 70283622448392425634745541)
        ·
          refine ⟨13178179209073579806514789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70283622448392425634745541 13178179209073579806514789)
          ·
            refine ⟨2470908601701296213721523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13178179209073579806514789 2470908601701296213721523)
            ·
              refine ⟨3706362902551944320582285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2470908601701296213721523 3706362902551944320582285)
              ·
                refine ⟨1389886088456979120218357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3706362902551944320582285 1389886088456979120218357)
                ·
                  refine ⟨130301820792841792520471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1389886088456979120218357 130301820792841792520471)
                  ·
                    rfl

theorem cell23_2283857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 5].length) (baseStart_2283857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283857 prefixEnd_2283857 := by exact prefixLift 2283857
  have htrace : WordTrace (prefixWord ++ tailWord_2283857) baseStart_2283857 baseEnd_2283857 := by
    simpa [prefixWord, tailWord_2283857, baseEnd_2283857] using wordTrace_append hprefix tailTrace_2283857
  have hstable : (prefixWord ++ tailWord_2283857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283857).length < 2 ^ (prefixWord ++ tailWord_2283857).sum := by decide
  have hdescent : baseEnd_2283857 < baseStart_2283857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283863 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 5]
def baseStart_2283863 : Nat := 118140960795 + 2283863 * 2 ^ 59
def prefixEnd_2283863 : Nat := 4983230072969 + 3 ^ 40 * 2283863 * 2
def baseEnd_2283863 : Nat := 1172719468019503109209211

theorem tailTrace_2283863 : CollatzResearch.WordTrace tailWord_2283863 prefixEnd_2283863 1172719468019503109209211 := by
  unfold tailWord_2283863
  simp only [CollatzResearch.WordTrace]
  refine ⟨83299326924961878591824243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55532884616641252394549495 83299326924961878591824243)
  ·
    refine ⟨124948990387442817887736365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83299326924961878591824243 124948990387442817887736365)
    ·
      refine ⟨46855871395291056707901137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124948990387442817887736365 46855871395291056707901137)
      ·
        refine ⟨35141903546468292530925853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46855871395291056707901137 35141903546468292530925853)
        ·
          refine ⟨13178213829925609699097195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35141903546468292530925853 13178213829925609699097195)
          ·
            refine ⟨19767320744888414548645793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13178213829925609699097195 19767320744888414548645793)
            ·
              refine ⟨14825490558666310911484345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19767320744888414548645793 14825490558666310911484345)
              ·
                refine ⟨11119117918999733183613259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14825490558666310911484345 11119117918999733183613259)
                ·
                  refine ⟨16678676878499599775419889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11119117918999733183613259 16678676878499599775419889)
                  ·
                    refine ⟨12509007658874699831564917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16678676878499599775419889 12509007658874699831564917)
                    ·
                      refine ⟨1172719468019503109209211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12509007658874699831564917 1172719468019503109209211)
                      ·
                        rfl

theorem cell23_2283863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_2283863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283863 prefixEnd_2283863 := by exact prefixLift 2283863
  have htrace : WordTrace (prefixWord ++ tailWord_2283863) baseStart_2283863 baseEnd_2283863 := by
    simpa [prefixWord, tailWord_2283863, baseEnd_2283863] using wordTrace_append hprefix tailTrace_2283863
  have hstable : (prefixWord ++ tailWord_2283863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283863).length < 2 ^ (prefixWord ++ tailWord_2283863).sum := by decide
  have hdescent : baseEnd_2283863 < baseStart_2283863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283874 : List Nat := [3, 3, 2, 1, 1, 3, 3, 2, 5]
def baseStart_2283874 : Nat := 118140960795 + 2283874 * 2 ^ 59
def prefixEnd_2283874 : Nat := 4983230072969 + 3 ^ 40 * 2283874 * 2
def baseEnd_2283874 : Nat := 130302790700744729574629

theorem tailTrace_2283874 : CollatzResearch.WordTrace tailWord_2283874 prefixEnd_2283874 130302790700744729574629 := by
  unfold tailWord_2283874
  simp only [CollatzResearch.WordTrace]
  refine ⟨20824932031980506867618669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55533152085281351646983117 20824932031980506867618669)
  ·
    refine ⟨7809349511992690075357001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20824932031980506867618669 7809349511992690075357001)
    ·
      refine ⟨5857012133994517556517751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7809349511992690075357001 5857012133994517556517751)
      ·
        refine ⟨8785518200991776334776627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5857012133994517556517751 8785518200991776334776627)
        ·
          refine ⟨13178277301487664502164941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8785518200991776334776627 13178277301487664502164941)
          ·
            refine ⟨4941853988057874188311853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13178277301487664502164941 4941853988057874188311853)
            ·
              refine ⟨1853195245521702820616945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4941853988057874188311853 1853195245521702820616945)
              ·
                refine ⟨1389896434141277115462709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1853195245521702820616945 1389896434141277115462709)
                ·
                  refine ⟨130302790700744729574629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1389896434141277115462709 130302790700744729574629)
                  ·
                    rfl

theorem cell23_2283874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_2283874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283874 prefixEnd_2283874 := by exact prefixLift 2283874
  have htrace : WordTrace (prefixWord ++ tailWord_2283874) baseStart_2283874 baseEnd_2283874 := by
    simpa [prefixWord, tailWord_2283874, baseEnd_2283874] using wordTrace_append hprefix tailTrace_2283874
  have hstable : (prefixWord ++ tailWord_2283874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283874).length < 2 ^ (prefixWord ++ tailWord_2283874).sum := by decide
  have hdescent : baseEnd_2283874 < baseStart_2283874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283880 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_2283880 : Nat := 118140960795 + 2283880 * 2 ^ 59
def prefixEnd_2283880 : Nat := 4983230072969 + 3 ^ 40 * 2283880 * 2
def baseEnd_2283880 : Nat := 1172728197190629542696633

theorem tailTrace_2283880 : CollatzResearch.WordTrace tailWord_2283880 prefixEnd_2283880 1172728197190629542696633 := by
  unfold tailWord_2283880
  simp only [CollatzResearch.WordTrace]
  refine ⟨41649973482950145247596547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55533297977266860330128729 41649973482950145247596547)
  ·
    refine ⟨62474960224425217871394821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41649973482950145247596547 62474960224425217871394821)
    ·
      refine ⟨11714055042079728350886529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62474960224425217871394821 11714055042079728350886529)
      ·
        refine ⟨8785541281559796263164897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11714055042079728350886529 8785541281559796263164897)
        ·
          refine ⟨6589155961169847197373673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8785541281559796263164897 6589155961169847197373673)
          ·
            refine ⟨4941866970877385398030255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6589155961169847197373673 4941866970877385398030255)
            ·
              refine ⟨7412800456316078097045383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4941866970877385398030255 7412800456316078097045383)
              ·
                refine ⟨11119200684474117145568075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7412800456316078097045383 11119200684474117145568075)
                ·
                  refine ⟨16678801026711175718352113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11119200684474117145568075 16678801026711175718352113)
                  ·
                    refine ⟨12509100770033381788764085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16678801026711175718352113 12509100770033381788764085)
                    ·
                      refine ⟨1172728197190629542696633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12509100770033381788764085 1172728197190629542696633)
                      ·
                        rfl

theorem cell23_2283880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_2283880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283880 prefixEnd_2283880 := by exact prefixLift 2283880
  have htrace : WordTrace (prefixWord ++ tailWord_2283880) baseStart_2283880 baseEnd_2283880 := by
    simpa [prefixWord, tailWord_2283880, baseEnd_2283880] using wordTrace_append hprefix tailTrace_2283880
  have hstable : (prefixWord ++ tailWord_2283880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283880).length < 2 ^ (prefixWord ++ tailWord_2283880).sum := by decide
  have hdescent : baseEnd_2283880 < baseStart_2283880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283907 : List Nat := [1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 4]
def baseStart_2283907 : Nat := 118140960795 + 2283907 * 2 ^ 59
def prefixEnd_2283907 : Nat := 4983230072969 + 3 ^ 40 * 2283907 * 2
def baseEnd_2283907 : Nat := 1172742061168300937059009

theorem tailTrace_2283907 : CollatzResearch.WordTrace tailWord_2283907 prefixEnd_2283907 1172742061168300937059009 := by
  unfold tailWord_2283907
  simp only [CollatzResearch.WordTrace]
  refine ⟨83300931736802474106425975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55533954491201649404283983 83300931736802474106425975)
  ·
    refine ⟨124951397605203711159638963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83300931736802474106425975 124951397605203711159638963)
    ·
      refine ⟨187427096407805566739458445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124951397605203711159638963 187427096407805566739458445)
      ·
        refine ⟨70285161152927087527296917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187427096407805566739458445 70285161152927087527296917)
        ·
          refine ⟨3294616929043457227842043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 70285161152927087527296917 3294616929043457227842043)
          ·
            refine ⟨4941925393565185841763065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3294616929043457227842043 4941925393565185841763065)
            ·
              refine ⟨3706444045173889381322299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4941925393565185841763065 3706444045173889381322299)
              ·
                refine ⟨5559666067760834071983449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3706444045173889381322299 5559666067760834071983449)
                ·
                  refine ⟨4169749550820625553987587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5559666067760834071983449 4169749550820625553987587)
                  ·
                    refine ⟨6254624326230938330981381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4169749550820625553987587 6254624326230938330981381)
                    ·
                      refine ⟨1172742061168300937059009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6254624326230938330981381 1172742061168300937059009)
                      ·
                        rfl

theorem cell23_2283907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_2283907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283907 prefixEnd_2283907 := by exact prefixLift 2283907
  have htrace : WordTrace (prefixWord ++ tailWord_2283907) baseStart_2283907 baseEnd_2283907 := by
    simpa [prefixWord, tailWord_2283907, baseEnd_2283907] using wordTrace_append hprefix tailTrace_2283907
  have hstable : (prefixWord ++ tailWord_2283907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283907).length < 2 ^ (prefixWord ++ tailWord_2283907).sum := by decide
  have hdescent : baseEnd_2283907 < baseStart_2283907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283930 : List Nat := [3, 1, 1, 4, 1, 2, 1, 4, 6]
def baseStart_2283930 : Nat := 118140960795 + 2283930 * 2 ^ 59
def prefixEnd_2283930 : Nat := 4983230072969 + 3 ^ 40 * 2283930 * 2
def baseEnd_2283930 : Nat := 130305985691483816341267

theorem tailTrace_2283930 : CollatzResearch.WordTrace tailWord_2283930 prefixEnd_2283930 130305985691483816341267 := by
  unfold tailWord_2283930
  simp only [CollatzResearch.WordTrace]
  refine ⟨20825442653929787258628311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55534513743812766023008829 20825442653929787258628311)
  ·
    refine ⟨31238163980894680887942467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20825442653929787258628311 31238163980894680887942467)
    ·
      refine ⟨46857245971342021331913701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31238163980894680887942467 46857245971342021331913701)
      ·
        refine ⟨8785733619626628999733819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46857245971342021331913701 8785733619626628999733819)
        ·
          refine ⟨13178600429439943499600729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8785733619626628999733819 13178600429439943499600729)
          ·
            refine ⟨9883950322079957624700547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13178600429439943499600729 9883950322079957624700547)
            ·
              refine ⟨14825925483119936437050821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9883950322079957624700547 14825925483119936437050821)
              ·
                refine ⟨2779861028084988081947029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14825925483119936437050821 2779861028084988081947029)
                ·
                  refine ⟨130305985691483816341267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2779861028084988081947029 130305985691483816341267)
                  ·
                    rfl

theorem cell23_2283930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 6].length) (baseStart_2283930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283930 prefixEnd_2283930 := by exact prefixLift 2283930
  have htrace : WordTrace (prefixWord ++ tailWord_2283930) baseStart_2283930 baseEnd_2283930 := by
    simpa [prefixWord, tailWord_2283930, baseEnd_2283930] using wordTrace_append hprefix tailTrace_2283930
  have hstable : (prefixWord ++ tailWord_2283930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283930).length < 2 ^ (prefixWord ++ tailWord_2283930).sum := by decide
  have hdescent : baseEnd_2283930 < baseStart_2283930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283960 : List Nat := [2, 1, 2, 1, 2, 2, 1, 6, 1, 5]
def baseStart_2283960 : Nat := 118140960795 + 2283960 * 2 ^ 59
def prefixEnd_2283960 : Nat := 4983230072969 + 3 ^ 40 * 2283960 * 2
def baseEnd_2283960 : Nat := 390923091880996409898755

theorem tailTrace_2283960 : CollatzResearch.WordTrace tailWord_2283960 prefixEnd_2283960 390923091880996409898755 := by
  unfold tailWord_2283960
  simp only [CollatzResearch.WordTrace]
  refine ⟨41651432402805232079052667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55535243203740309438736889 41651432402805232079052667)
  ·
    refine ⟨62477148604207848118579001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41651432402805232079052667 62477148604207848118579001)
    ·
      refine ⟨46857861453155886088934251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62477148604207848118579001 46857861453155886088934251)
      ·
        refine ⟨70286792179733829133401377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46857861453155886088934251 70286792179733829133401377)
        ·
          refine ⟨52715094134800371850051033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70286792179733829133401377 52715094134800371850051033)
          ·
            refine ⟨39536320601100278887538275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52715094134800371850051033 39536320601100278887538275)
            ·
              refine ⟨59304480901650418331307413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39536320601100278887538275 59304480901650418331307413)
              ·
                refine ⟨2779897542264863359280035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59304480901650418331307413 2779897542264863359280035)
                ·
                  refine ⟨4169846313397295038920053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2779897542264863359280035 4169846313397295038920053)
                  ·
                    refine ⟨390923091880996409898755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4169846313397295038920053 390923091880996409898755)
                    ·
                      rfl

theorem cell23_2283960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_2283960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283960 prefixEnd_2283960 := by exact prefixLift 2283960
  have htrace : WordTrace (prefixWord ++ tailWord_2283960) baseStart_2283960 baseEnd_2283960 := by
    simpa [prefixWord, tailWord_2283960, baseEnd_2283960] using wordTrace_append hprefix tailTrace_2283960
  have hstable : (prefixWord ++ tailWord_2283960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283960).length < 2 ^ (prefixWord ++ tailWord_2283960).sum := by decide
  have hdescent : baseEnd_2283960 < baseStart_2283960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283963 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 4]
def baseStart_2283963 : Nat := 118140960795 + 2283963 * 2 ^ 59
def prefixEnd_2283963 : Nat := 4983230072969 + 3 ^ 40 * 2283963 * 2
def baseEnd_2283963 : Nat := 1172770816084952717958751

theorem tailTrace_2283963 : CollatzResearch.WordTrace tailWord_2283963 prefixEnd_2283963 1172770816084952717958751 := by
  unfold tailWord_2283963
  simp only [CollatzResearch.WordTrace]
  refine ⟨83302974224599595670464543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55535316149733063780309695 83302974224599595670464543)
  ·
    refine ⟨124954461336899393505696815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83302974224599595670464543 124954461336899393505696815)
    ·
      refine ⟨187431692005349090258545223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124954461336899393505696815 187431692005349090258545223)
      ·
        refine ⟨281147538008023635387817835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187431692005349090258545223 281147538008023635387817835)
        ·
          refine ⟨421721307012035453081726753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281147538008023635387817835 421721307012035453081726753)
          ·
            refine ⟨316290980259026589811295065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 421721307012035453081726753 316290980259026589811295065)
            ·
              refine ⟨237218235194269942358471299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316290980259026589811295065 237218235194269942358471299)
              ·
                refine ⟨355827352791404913537706949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237218235194269942358471299 355827352791404913537706949)
                ·
                  refine ⟨66717628648388421288320053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 355827352791404913537706949 66717628648388421288320053)
                  ·
                    refine ⟨6254777685786414495780005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66717628648388421288320053 6254777685786414495780005)
                    ·
                      refine ⟨1172770816084952717958751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6254777685786414495780005 1172770816084952717958751)
                      ·
                        rfl

theorem cell23_2283963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 4].length) (baseStart_2283963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283963 prefixEnd_2283963 := by exact prefixLift 2283963
  have htrace : WordTrace (prefixWord ++ tailWord_2283963) baseStart_2283963 baseEnd_2283963 := by
    simpa [prefixWord, tailWord_2283963, baseEnd_2283963] using wordTrace_append hprefix tailTrace_2283963
  have hstable : (prefixWord ++ tailWord_2283963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283963).length < 2 ^ (prefixWord ++ tailWord_2283963).sum := by decide
  have hdescent : baseEnd_2283963 < baseStart_2283963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283977 : List Nat := [1, 2, 1, 1, 2, 1, 8, 1, 1, 5]
def baseStart_2283977 : Nat := 118140960795 + 2283977 * 2 ^ 59
def prefixEnd_2283977 : Nat := 4983230072969 + 3 ^ 40 * 2283977 * 2
def baseEnd_2283977 : Nat := 390926001604705221061229

theorem tailTrace_2283977 : CollatzResearch.WordTrace tailWord_2283977 prefixEnd_2283977 390926001604705221061229 := by
  unfold tailWord_2283977
  simp only [CollatzResearch.WordTrace]
  refine ⟨83303484846548876061474185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55535656564365917374316123 83303484846548876061474185)
  ·
    refine ⟨62477613634911657046105639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83303484846548876061474185 62477613634911657046105639)
    ·
      refine ⟨93716420452367485569158459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62477613634911657046105639 93716420452367485569158459)
      ·
        refine ⟨140574630678551228353737689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93716420452367485569158459 140574630678551228353737689)
        ·
          refine ⟨105430973008913421265303267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140574630678551228353737689 105430973008913421265303267)
          ·
            refine ⟨158146459513370131897954901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105430973008913421265303267 158146459513370131897954901)
            ·
              refine ⟨1853278822422306233179159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 158146459513370131897954901 1853278822422306233179159)
              ·
                refine ⟨2779918233633459349768739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1853278822422306233179159 2779918233633459349768739)
                ·
                  refine ⟨4169877350450189024653109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2779918233633459349768739 4169877350450189024653109)
                  ·
                    refine ⟨390926001604705221061229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4169877350450189024653109 390926001604705221061229)
                    ·
                      rfl

theorem cell23_2283977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 1, 5].length) (baseStart_2283977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2283977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2283977 prefixEnd_2283977 := by exact prefixLift 2283977
  have htrace : WordTrace (prefixWord ++ tailWord_2283977) baseStart_2283977 baseEnd_2283977 := by
    simpa [prefixWord, tailWord_2283977, baseEnd_2283977] using wordTrace_append hprefix tailTrace_2283977
  have hstable : (prefixWord ++ tailWord_2283977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283977).length < 2 ^ (prefixWord ++ tailWord_2283977).sum := by decide
  have hdescent : baseEnd_2283977 < baseStart_2283977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284000 : List Nat := [2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 5]
def baseStart_2284000 : Nat := 118140960795 + 2284000 * 2 ^ 59
def prefixEnd_2284000 : Nat := 4983230072969 + 3 ^ 40 * 2284000 * 2
def baseEnd_2284000 : Nat := 1172789814869169073196081

theorem tailTrace_2284000 : CollatzResearch.WordTrace tailWord_2284000 prefixEnd_2284000 1172789814869169073196081 := by
  unfold tailWord_2284000
  simp only [CollatzResearch.WordTrace]
  refine ⟨41652161862732775494780727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55536215816977033993040969 41652161862732775494780727)
  ·
    refine ⟨62478242794099163242171091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41652161862732775494780727 62478242794099163242171091)
    ·
      refine ⟨93717364191148744863256637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62478242794099163242171091 93717364191148744863256637)
      ·
        refine ⟨35144011571680779323721239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93717364191148744863256637 35144011571680779323721239)
        ·
          refine ⟨52716017357521168985581859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35144011571680779323721239 52716017357521168985581859)
          ·
            refine ⟨79074026036281753478372789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52716017357521168985581859 79074026036281753478372789)
            ·
              refine ⟨7413189940901414388597449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79074026036281753478372789 7413189940901414388597449)
              ·
                refine ⟨5559892455676060791448087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7413189940901414388597449 5559892455676060791448087)
                ·
                  refine ⟨8339838683514091187172131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5559892455676060791448087 8339838683514091187172131)
                  ·
                    refine ⟨12509758025271136780758197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8339838683514091187172131 12509758025271136780758197)
                    ·
                      refine ⟨1172789814869169073196081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12509758025271136780758197 1172789814869169073196081)
                      ·
                        rfl

theorem cell23_2284000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_2284000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284000 prefixEnd_2284000 := by exact prefixLift 2284000
  have htrace : WordTrace (prefixWord ++ tailWord_2284000) baseStart_2284000 baseEnd_2284000 := by
    simpa [prefixWord, tailWord_2284000, baseEnd_2284000] using wordTrace_append hprefix tailTrace_2284000
  have hstable : (prefixWord ++ tailWord_2284000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284000).length < 2 ^ (prefixWord ++ tailWord_2284000).sum := by decide
  have hdescent : baseEnd_2284000 < baseStart_2284000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284014 : List Nat := [4, 1, 2, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_2284014 : Nat := 118140960795 + 2284014 * 2 ^ 59
def prefixEnd_2284014 : Nat := 4983230072969 + 3 ^ 40 * 2284014 * 2
def baseEnd_2284014 : Nat := 1172797003598332018421017

theorem tailTrace_2284014 : CollatzResearch.WordTrace tailWord_2284014 prefixEnd_2284014 1172797003598332018421017 := by
  unfold tailWord_2284014
  simp only [CollatzResearch.WordTrace]
  refine ⟨10413104293426853922571387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55536556231609887587047397 10413104293426853922571387)
  ·
    refine ⟨15619656440140280883857081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10413104293426853922571387 15619656440140280883857081)
    ·
      refine ⟨11714742330105210662892811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15619656440140280883857081 11714742330105210662892811)
      ·
        refine ⟨17572113495157815994339217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11714742330105210662892811 17572113495157815994339217)
        ·
          refine ⟨13179085121368361995754413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17572113495157815994339217 13179085121368361995754413)
          ·
            refine ⟨4942156920513135748407905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13179085121368361995754413 4942156920513135748407905)
            ·
              refine ⟨3706617690384851811305929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4942156920513135748407905 3706617690384851811305929)
              ·
                refine ⟨2779963267788638858479447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3706617690384851811305929 2779963267788638858479447)
                ·
                  refine ⟨4169944901682958287719171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2779963267788638858479447 4169944901682958287719171)
                  ·
                    refine ⟨6254917352524437431578757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4169944901682958287719171 6254917352524437431578757)
                    ·
                      refine ⟨1172797003598332018421017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6254917352524437431578757 1172797003598332018421017)
                      ·
                        rfl

theorem cell23_2284014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_2284014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284014 prefixEnd_2284014 := by exact prefixLift 2284014
  have htrace : WordTrace (prefixWord ++ tailWord_2284014) baseStart_2284014 baseEnd_2284014 := by
    simpa [prefixWord, tailWord_2284014, baseEnd_2284014] using wordTrace_append hprefix tailTrace_2284014
  have hstable : (prefixWord ++ tailWord_2284014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284014).length < 2 ^ (prefixWord ++ tailWord_2284014).sum := by decide
  have hdescent : baseEnd_2284014 < baseStart_2284014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284057 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 5, 3, 2]
def baseStart_2284057 : Nat := 118140960795 + 2284057 * 2 ^ 59
def prefixEnd_2284057 : Nat := 4983230072969 + 3 ^ 40 * 2284057 * 2
def baseEnd_2284057 : Nat := 1172819083266475350183319

theorem tailTrace_2284057 : CollatzResearch.WordTrace tailWord_2284057 prefixEnd_2284057 1172819083266475350183319 := by
  unfold tailWord_2284057
  simp only [CollatzResearch.WordTrace]
  refine ⟨83306402686259049724386425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55537601790839366482924283 83306402686259049724386425)
  ·
    refine ⟨62479802014694287293289819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83306402686259049724386425 62479802014694287293289819)
    ·
      refine ⟨93719703022041430939934729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62479802014694287293289819 93719703022041430939934729)
      ·
        refine ⟨70289777266531073204951047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93719703022041430939934729 70289777266531073204951047)
        ·
          refine ⟨105434665899796609807426571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70289777266531073204951047 105434665899796609807426571)
          ·
            refine ⟨158151998849694914711139857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105434665899796609807426571 158151998849694914711139857)
            ·
              refine ⟨118613999137271186033354893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158151998849694914711139857 118613999137271186033354893)
              ·
                refine ⟨44480249676476694762508085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118613999137271186033354893 44480249676476694762508085)
                ·
                  refine ⟨4170023407169690133985133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44480249676476694762508085 4170023407169690133985133)
                  ·
                    refine ⟨1563758777688633800244425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4170023407169690133985133 1563758777688633800244425)
                    ·
                      refine ⟨1172819083266475350183319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1563758777688633800244425 1172819083266475350183319)
                      ·
                        rfl

theorem cell23_2284057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 3, 2].length) (baseStart_2284057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284057 prefixEnd_2284057 := by exact prefixLift 2284057
  have htrace : WordTrace (prefixWord ++ tailWord_2284057) baseStart_2284057 baseEnd_2284057 := by
    simpa [prefixWord, tailWord_2284057, baseEnd_2284057] using wordTrace_append hprefix tailTrace_2284057
  have hstable : (prefixWord ++ tailWord_2284057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284057).length < 2 ^ (prefixWord ++ tailWord_2284057).sum := by decide
  have hdescent : baseEnd_2284057 < baseStart_2284057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284068 : List Nat := [2, 3, 1, 5, 1, 2, 1, 2, 1, 2, 3]
def baseStart_2284068 : Nat := 118140960795 + 2284068 * 2 ^ 59
def prefixEnd_2284068 : Nat := 4983230072969 + 3 ^ 40 * 2284068 * 2
def baseEnd_2284068 : Nat := 1172824731553674807145769

theorem tailTrace_2284068 : CollatzResearch.WordTrace tailWord_2284068 prefixEnd_2284068 1172824731553674807145769 := by
  unfold tailWord_2284068
  simp only [CollatzResearch.WordTrace]
  refine ⟨41653401944609599301518429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55537869259479465735357905 41653401944609599301518429)
  ·
    refine ⟨15620025729228599738069411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41653401944609599301518429 15620025729228599738069411)
    ·
      refine ⟨23430038593842899607104117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15620025729228599738069411 23430038593842899607104117)
      ·
        refine ⟨2196566118172771838166011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23430038593842899607104117 2196566118172771838166011)
        ·
          refine ⟨3294849177259157757249017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2196566118172771838166011 3294849177259157757249017)
          ·
            refine ⟨2471136882944368317936763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3294849177259157757249017 2471136882944368317936763)
            ·
              refine ⟨3706705324416552476905145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2471136882944368317936763 3706705324416552476905145)
              ·
                refine ⟨2780028993312414357678859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3706705324416552476905145 2780028993312414357678859)
                ·
                  refine ⟨4170043489968621536518289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2780028993312414357678859 4170043489968621536518289)
                  ·
                    refine ⟨3127532617476466152388717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4170043489968621536518289 3127532617476466152388717)
                    ·
                      refine ⟨1172824731553674807145769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3127532617476466152388717 1172824731553674807145769)
                      ·
                        rfl

theorem cell23_2284068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_2284068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284068 prefixEnd_2284068 := by exact prefixLift 2284068
  have htrace : WordTrace (prefixWord ++ tailWord_2284068) baseStart_2284068 baseEnd_2284068 := by
    simpa [prefixWord, tailWord_2284068, baseEnd_2284068] using wordTrace_append hprefix tailTrace_2284068
  have hstable : (prefixWord ++ tailWord_2284068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284068).length < 2 ^ (prefixWord ++ tailWord_2284068).sum := by decide
  have hdescent : baseEnd_2284068 < baseStart_2284068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284104 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 4, 2, 2]
def baseStart_2284104 : Nat := 118140960795 + 2284104 * 2 ^ 59
def prefixEnd_2284104 : Nat := 4983230072969 + 3 ^ 40 * 2284104 * 2
def baseEnd_2284104 : Nat := 1172843216857236666295603

theorem tailTrace_2284104 : CollatzResearch.WordTrace tailWord_2284104 prefixEnd_2284104 1172843216857236666295603 := by
  unfold tailWord_2284104
  simp only [CollatzResearch.WordTrace]
  refine ⟨41654058458544388375673683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55538744611392517834231577 41654058458544388375673683)
  ·
    refine ⟨62481087687816582563510525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41654058458544388375673683 62481087687816582563510525)
    ·
      refine ⟨23430407882931218461316447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62481087687816582563510525 23430407882931218461316447)
      ·
        refine ⟨35145611824396827691974671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23430407882931218461316447 35145611824396827691974671)
        ·
          refine ⟨52718417736595241537962007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35145611824396827691974671 52718417736595241537962007)
          ·
            refine ⟨79077626604892862306943011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52718417736595241537962007 79077626604892862306943011)
            ·
              refine ⟨118616439907339293460414517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79077626604892862306943011 118616439907339293460414517)
              ·
                refine ⟨11120291241313058761913861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 118616439907339293460414517 11120291241313058761913861)
                ·
                  refine ⟨2085054607746198517858849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11120291241313058761913861 2085054607746198517858849)
                  ·
                    refine ⟨1563790955809648888394137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2085054607746198517858849 1563790955809648888394137)
                    ·
                      refine ⟨1172843216857236666295603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1563790955809648888394137 1172843216857236666295603)
                      ·
                        rfl

theorem cell23_2284104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_2284104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284104 prefixEnd_2284104 := by exact prefixLift 2284104
  have htrace : WordTrace (prefixWord ++ tailWord_2284104) baseStart_2284104 baseEnd_2284104 := by
    simpa [prefixWord, tailWord_2284104, baseEnd_2284104] using wordTrace_append hprefix tailTrace_2284104
  have hstable : (prefixWord ++ tailWord_2284104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284104).length < 2 ^ (prefixWord ++ tailWord_2284104).sum := by decide
  have hdescent : baseEnd_2284104 < baseStart_2284104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284147 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 1, 7, 2]
def baseStart_2284147 : Nat := 118140960795 + 2284147 * 2 ^ 59
def prefixEnd_2284147 : Nat := 4983230072969 + 3 ^ 40 * 2284147 * 2
def baseEnd_2284147 : Nat := 1172865296525379998057905

theorem tailTrace_2284147 : CollatzResearch.WordTrace tailWord_2284147 prefixEnd_2284147 1172865296525379998057905 := by
  unfold tailWord_2284147
  simp only [CollatzResearch.WordTrace]
  refine ⟨83309685255932995095162695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55539790170621996730108463 83309685255932995095162695)
  ·
    refine ⟨124964527883899492642744043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83309685255932995095162695 124964527883899492642744043)
    ·
      refine ⟨187446791825849238964116065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124964527883899492642744043 187446791825849238964116065)
      ·
        refine ⟨140585093869386929223087049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187446791825849238964116065 140585093869386929223087049)
        ·
          refine ⟨105438820402040196917315287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140585093869386929223087049 105438820402040196917315287)
          ·
            refine ⟨158158230603060295375972931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105438820402040196917315287 158158230603060295375972931)
            ·
              refine ⟨237237345904590443063959397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158158230603060295375972931 237237345904590443063959397)
              ·
                refine ⟨44482002357110708074492387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 237237345904590443063959397 44482002357110708074492387)
                ·
                  refine ⟨66723003535666062111738581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44482002357110708074492387 66723003535666062111738581)
                  ·
                    refine ⟨1563820395367173330743873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 66723003535666062111738581 1563820395367173330743873)
                    ·
                      refine ⟨1172865296525379998057905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1563820395367173330743873 1172865296525379998057905)
                      ·
                        rfl

theorem cell23_2284147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 7, 2].length) (baseStart_2284147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284147 prefixEnd_2284147 := by exact prefixLift 2284147
  have htrace : WordTrace (prefixWord ++ tailWord_2284147) baseStart_2284147 baseEnd_2284147 := by
    simpa [prefixWord, tailWord_2284147, baseEnd_2284147] using wordTrace_append hprefix tailTrace_2284147
  have hstable : (prefixWord ++ tailWord_2284147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284147).length < 2 ^ (prefixWord ++ tailWord_2284147).sum := by decide
  have hdescent : baseEnd_2284147 < baseStart_2284147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284217 : List Nat := [1, 2, 1, 4, 1, 1, 1, 6, 6]
def baseStart_2284217 : Nat := 118140960795 + 2284217 * 2 ^ 59
def prefixEnd_2284217 : Nat := 4983230072969 + 3 ^ 40 * 2284217 * 2
def baseEnd_2284217 : Nat := 130322360019021636020287

theorem tailTrace_2284217 : CollatzResearch.WordTrace tailWord_2284217 prefixEnd_2284217 130322360019021636020287 := by
  unfold tailWord_2284217
  simp only [CollatzResearch.WordTrace]
  refine ⟨83312238365679397050210905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55541492243786264700140603 83312238365679397050210905)
  ·
    refine ⟨62484178774259547787658179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83312238365679397050210905 62484178774259547787658179)
    ·
      refine ⟨93726268161389321681487269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62484178774259547787658179 93726268161389321681487269)
      ·
        refine ⟨17573675280260497815278863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93726268161389321681487269 17573675280260497815278863)
        ·
          refine ⟨26360512920390746722918295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17573675280260497815278863 26360512920390746722918295)
          ·
            refine ⟨39540769380586120084377443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26360512920390746722918295 39540769380586120084377443)
            ·
              refine ⟨59311154070879180126566165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39540769380586120084377443 59311154070879180126566165)
              ·
                refine ⟨2780210347072461568432789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59311154070879180126566165 2780210347072461568432789)
                ·
                  refine ⟨130322360019021636020287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2780210347072461568432789 130322360019021636020287)
                  ·
                    rfl

theorem cell23_2284217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 6].length) (baseStart_2284217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284217 prefixEnd_2284217 := by exact prefixLift 2284217
  have htrace : WordTrace (prefixWord ++ tailWord_2284217) baseStart_2284217 baseEnd_2284217 := by
    simpa [prefixWord, tailWord_2284217, baseEnd_2284217] using wordTrace_append hprefix tailTrace_2284217
  have hstable : (prefixWord ++ tailWord_2284217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284217).length < 2 ^ (prefixWord ++ tailWord_2284217).sum := by decide
  have hdescent : baseEnd_2284217 < baseStart_2284217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284221 : List Nat := [1, 4, 1, 2, 1, 5, 1, 1, 3, 4]
def baseStart_2284221 : Nat := 118140960795 + 2284221 * 2 ^ 59
def prefixEnd_2284221 : Nat := 4983230072969 + 3 ^ 40 * 2284221 * 2
def baseEnd_2284221 : Nat := 390967764697937569510855

theorem tailTrace_2284221 : CollatzResearch.WordTrace tailWord_2284221 prefixEnd_2284221 390967764697937569510855 := by
  unfold tailWord_2284221
  simp only [CollatzResearch.WordTrace]
  refine ⟨83312384257664905733356517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55541589505109937155571011 83312384257664905733356517)
  ·
    refine ⟨15621072048312169825004347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83312384257664905733356517 15621072048312169825004347)
    ·
      refine ⟨23431608072468254737506521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15621072048312169825004347 23431608072468254737506521)
      ·
        refine ⟨17573706054351191053129891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23431608072468254737506521 17573706054351191053129891)
        ·
          refine ⟨26360559081526786579694837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17573706054351191053129891 26360559081526786579694837)
          ·
            refine ⟨2471302413893136241846391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26360559081526786579694837 2471302413893136241846391)
            ·
              refine ⟨3706953620839704362769587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2471302413893136241846391 3706953620839704362769587)
              ·
                refine ⟨5560430431259556544154381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3706953620839704362769587 5560430431259556544154381)
                ·
                  refine ⟨2085161411722333704057893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5560430431259556544154381 2085161411722333704057893)
                  ·
                    refine ⟨390967764697937569510855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2085161411722333704057893 390967764697937569510855)
                    ·
                      rfl

theorem cell23_2284221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_2284221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284221 prefixEnd_2284221 := by exact prefixLift 2284221
  have htrace : WordTrace (prefixWord ++ tailWord_2284221) baseStart_2284221 baseEnd_2284221 := by
    simpa [prefixWord, tailWord_2284221, baseEnd_2284221] using wordTrace_append hprefix tailTrace_2284221
  have hstable : (prefixWord ++ tailWord_2284221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284221).length < 2 ^ (prefixWord ++ tailWord_2284221).sum := by decide
  have hdescent : baseEnd_2284221 < baseStart_2284221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284234 : List Nat := [3, 1, 2, 1, 4, 2, 1, 3, 6]
def baseStart_2284234 : Nat := 118140960795 + 2284234 * 2 ^ 59
def prefixEnd_2284234 : Nat := 4983230072969 + 3 ^ 40 * 2284234 * 2
def baseEnd_2284234 : Nat := 130323329926924573074445

theorem tailTrace_2284234 : CollatzResearch.WordTrace tailWord_2284234 prefixEnd_2284234 130323329926924573074445 := by
  unfold tailWord_2284234
  simp only [CollatzResearch.WordTrace]
  refine ⟨20828214601654452238394939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55541905604411872635719837 20828214601654452238394939)
  ·
    refine ⟨31242321902481678357592409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20828214601654452238394939 31242321902481678357592409)
    ·
      refine ⟨23431741426861258768194307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31242321902481678357592409 23431741426861258768194307)
      ·
        refine ⟨35147612140291888152291461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23431741426861258768194307 35147612140291888152291461)
        ·
          refine ⟨6590177276304729028554649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35147612140291888152291461 6590177276304729028554649)
          ·
            refine ⟨4942632957228546771415987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6590177276304729028554649 4942632957228546771415987)
            ·
              refine ⟨7413949435842820157123981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4942632957228546771415987 7413949435842820157123981)
              ·
                refine ⟨2780231038441057558921493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7413949435842820157123981 2780231038441057558921493)
                ·
                  refine ⟨130323329926924573074445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2780231038441057558921493 130323329926924573074445)
                  ·
                    rfl

theorem cell23_2284234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 6].length) (baseStart_2284234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284234 prefixEnd_2284234 := by exact prefixLift 2284234
  have htrace : WordTrace (prefixWord ++ tailWord_2284234) baseStart_2284234 baseEnd_2284234 := by
    simpa [prefixWord, tailWord_2284234, baseEnd_2284234] using wordTrace_append hprefix tailTrace_2284234
  have hstable : (prefixWord ++ tailWord_2284234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284234).length < 2 ^ (prefixWord ++ tailWord_2284234).sum := by decide
  have hdescent : baseEnd_2284234 < baseStart_2284234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284271 : List Nat := [1, 1, 2, 1, 5, 2, 2, 2, 2, 3, 2]
def baseStart_2284271 : Nat := 118140960795 + 2284271 * 2 ^ 59
def prefixEnd_2284271 : Nat := 4983230072969 + 3 ^ 40 * 2284271 * 2
def baseEnd_2284271 : Nat := 1172928968126537512907335

theorem tailTrace_2284271 : CollatzResearch.WordTrace tailWord_2284271 prefixEnd_2284271 1172928968126537512907335 := by
  unfold tailWord_2284271
  simp only [CollatzResearch.WordTrace]
  refine ⟨83314207907483764272676667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55542805271655842848451111 83314207907483764272676667)
  ·
    refine ⟨124971311861225646409015001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83314207907483764272676667 124971311861225646409015001)
    ·
      refine ⟨93728483895919234806761251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124971311861225646409015001 93728483895919234806761251)
      ·
        refine ⟨140592725843878852210141877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93728483895919234806761251 140592725843878852210141877)
        ·
          refine ⟨13180568047863642394700801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140592725843878852210141877 13180568047863642394700801)
          ·
            refine ⟨9885426035897731796025601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13180568047863642394700801 9885426035897731796025601)
            ·
              refine ⟨7414069526923298847019201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9885426035897731796025601 7414069526923298847019201)
              ·
                refine ⟨5560552145192474135264401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7414069526923298847019201 5560552145192474135264401)
                ·
                  refine ⟨4170414108894355601448301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5560552145192474135264401 4170414108894355601448301)
                  ·
                    refine ⟨1563905290835383350543113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4170414108894355601448301 1563905290835383350543113)
                    ·
                      refine ⟨1172928968126537512907335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1563905290835383350543113 1172928968126537512907335)
                      ·
                        rfl

theorem cell23_2284271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 3, 2].length) (baseStart_2284271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284271 prefixEnd_2284271 := by exact prefixLift 2284271
  have htrace : WordTrace (prefixWord ++ tailWord_2284271) baseStart_2284271 baseEnd_2284271 := by
    simpa [prefixWord, tailWord_2284271, baseEnd_2284271] using wordTrace_append hprefix tailTrace_2284271
  have hstable : (prefixWord ++ tailWord_2284271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284271).length < 2 ^ (prefixWord ++ tailWord_2284271).sum := by decide
  have hdescent : baseEnd_2284271 < baseStart_2284271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284284 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_2284284 : Nat := 118140960795 + 2284284 * 2 ^ 59
def prefixEnd_2284284 : Nat := 4983230072969 + 3 ^ 40 * 2284284 * 2
def baseEnd_2284284 : Nat := 1172935643375045962044775

theorem tailTrace_2284284 : CollatzResearch.WordTrace tailWord_2284284 prefixEnd_2284284 1172935643375045962044775 := by
  unfold tailWord_2284284
  simp only [CollatzResearch.WordTrace]
  refine ⟨41657341028218333746449953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55543121370957778328599937 41657341028218333746449953)
  ·
    refine ⟨31243005771163750309837465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41657341028218333746449953 31243005771163750309837465)
    ·
      refine ⟨23432254328372812732378099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31243005771163750309837465 23432254328372812732378099)
      ·
        refine ⟨35148381492559219098567149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23432254328372812732378099 35148381492559219098567149)
        ·
          refine ⟨13180643059709707161962681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35148381492559219098567149 13180643059709707161962681)
          ·
            refine ⟨9885482294782280371472011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13180643059709707161962681 9885482294782280371472011)
            ·
              refine ⟨14828223442173420557208017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9885482294782280371472011 14828223442173420557208017)
              ·
                refine ⟨11121167581630065417906013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14828223442173420557208017 11121167581630065417906013)
                ·
                  refine ⟨4170437843111274531714755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11121167581630065417906013 4170437843111274531714755)
                  ·
                    refine ⟨6255656764666911797572133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4170437843111274531714755 6255656764666911797572133)
                    ·
                      refine ⟨1172935643375045962044775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6255656764666911797572133 1172935643375045962044775)
                      ·
                        rfl

theorem cell23_2284284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_2284284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284284 prefixEnd_2284284 := by exact prefixLift 2284284
  have htrace : WordTrace (prefixWord ++ tailWord_2284284) baseStart_2284284 baseEnd_2284284 := by
    simpa [prefixWord, tailWord_2284284, baseEnd_2284284] using wordTrace_append hprefix tailTrace_2284284
  have hstable : (prefixWord ++ tailWord_2284284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284284).length < 2 ^ (prefixWord ++ tailWord_2284284).sum := by decide
  have hdescent : baseEnd_2284284 < baseStart_2284284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284287 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 5]
def baseStart_2284287 : Nat := 118140960795 + 2284287 * 2 ^ 59
def prefixEnd_2284287 : Nat := 4983230072969 + 3 ^ 40 * 2284287 * 2
def baseEnd_2284287 : Nat := 1172937183817009450307261

theorem tailTrace_2284287 : CollatzResearch.WordTrace tailWord_2284287 prefixEnd_2284287 1172937183817009450307261 := by
  unfold tailWord_2284287
  simp only [CollatzResearch.WordTrace]
  refine ⟨83314791475425799005259115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55543194316950532670172743 83314791475425799005259115)
  ·
    refine ⟨124972187213138698507888673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83314791475425799005259115 124972187213138698507888673)
    ·
      refine ⟨93729140409854023880916505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124972187213138698507888673 93729140409854023880916505)
      ·
        refine ⟨70296855307390517910687379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93729140409854023880916505 70296855307390517910687379)
        ·
          refine ⟨105445282961085776866031069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70296855307390517910687379 105445282961085776866031069)
          ·
            refine ⟨39541981110407166324761651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105445282961085776866031069 39541981110407166324761651)
            ·
              refine ⟨59312971665610749487142477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39541981110407166324761651 59312971665610749487142477)
              ·
                refine ⟨22242364374604031057678429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59312971665610749487142477 22242364374604031057678429)
                ·
                  refine ⟨8340886640476511646629411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22242364374604031057678429 8340886640476511646629411)
                  ·
                    refine ⟨12511329960714767469944117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8340886640476511646629411 12511329960714767469944117)
                    ·
                      refine ⟨1172937183817009450307261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12511329960714767469944117 1172937183817009450307261)
                      ·
                        rfl

theorem cell23_2284287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_2284287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284287 prefixEnd_2284287 := by exact prefixLift 2284287
  have htrace : WordTrace (prefixWord ++ tailWord_2284287) baseStart_2284287 baseEnd_2284287 := by
    simpa [prefixWord, tailWord_2284287, baseEnd_2284287] using wordTrace_append hprefix tailTrace_2284287
  have hstable : (prefixWord ++ tailWord_2284287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284287).length < 2 ^ (prefixWord ++ tailWord_2284287).sum := by decide
  have hdescent : baseEnd_2284287 < baseStart_2284287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284297 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 1, 1, 6]
def baseStart_2284297 : Nat := 118140960795 + 2284297 * 2 ^ 59
def prefixEnd_2284297 : Nat := 4983230072969 + 3 ^ 40 * 2284297 * 2
def baseEnd_2284297 : Nat := 1172942318623554411182215

theorem tailTrace_2284297 : CollatzResearch.WordTrace tailWord_2284297 prefixEnd_2284297 1172942318623554411182215 := by
  unfold tailWord_2284297
  simp only [CollatzResearch.WordTrace]
  refine ⟨83315156205389570713123145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55543437470259713808748763 83315156205389570713123145)
  ·
    refine ⟨62486367154042178034842359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83315156205389570713123145 62486367154042178034842359)
    ·
      refine ⟨93729550731063267052263539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62486367154042178034842359 93729550731063267052263539)
      ·
        refine ⟨140594326096594900578395309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93729550731063267052263539 140594326096594900578395309)
        ·
          refine ⟨52722872286223087716898241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140594326096594900578395309 52722872286223087716898241)
          ·
            refine ⟨39542154214667315787673681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52722872286223087716898241 39542154214667315787673681)
            ·
              refine ⟨29656615661000486840755261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39542154214667315787673681 29656615661000486840755261)
              ·
                refine ⟨11121230872875182565283223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29656615661000486840755261 11121230872875182565283223)
                ·
                  refine ⟨16681846309312773847924835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11121230872875182565283223 16681846309312773847924835)
                  ·
                    refine ⟨25022769463969160771887253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16681846309312773847924835 25022769463969160771887253)
                    ·
                      refine ⟨1172942318623554411182215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25022769463969160771887253 1172942318623554411182215)
                      ·
                        rfl

theorem cell23_2284297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_2284297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284297 prefixEnd_2284297 := by exact prefixLift 2284297
  have htrace : WordTrace (prefixWord ++ tailWord_2284297) baseStart_2284297 baseEnd_2284297 := by
    simpa [prefixWord, tailWord_2284297, baseEnd_2284297] using wordTrace_append hprefix tailTrace_2284297
  have hstable : (prefixWord ++ tailWord_2284297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284297).length < 2 ^ (prefixWord ++ tailWord_2284297).sum := by decide
  have hdescent : baseEnd_2284297 < baseStart_2284297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284314 : List Nat := [3, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4]
def baseStart_2284314 : Nat := 118140960795 + 2284314 * 2 ^ 59
def prefixEnd_2284314 : Nat := 4983230072969 + 3 ^ 40 * 2284314 * 2
def baseEnd_2284314 : Nat := 1172951047794680844669637

theorem tailTrace_2284314 : CollatzResearch.WordTrace tailWord_2284314 prefixEnd_2284314 1172951047794680844669637 := by
  unfold tailWord_2284314
  simp only [CollatzResearch.WordTrace]
  refine ⟨20828944061581995654122999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55543850830885321744327997 20828944061581995654122999)
  ·
    refine ⟨31243416092372993481184499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20828944061581995654122999 31243416092372993481184499)
    ·
      refine ⟨46865124138559490221776749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31243416092372993481184499 46865124138559490221776749)
      ·
        refine ⟨17574421551959808833166281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46865124138559490221776749 17574421551959808833166281)
        ·
          refine ⟨13180816163969856624874711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17574421551959808833166281 13180816163969856624874711)
          ·
            refine ⟨19771224245954784937312067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13180816163969856624874711 19771224245954784937312067)
            ·
              refine ⟨29656836368932177405968101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19771224245954784937312067 29656836368932177405968101)
              ·
                refine ⟨5560656819174783263619019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29656836368932177405968101 5560656819174783263619019)
                ·
                  refine ⟨8340985228762174895428529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5560656819174783263619019 8340985228762174895428529)
                  ·
                    refine ⟨6255738921571631171571397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8340985228762174895428529 6255738921571631171571397)
                    ·
                      refine ⟨1172951047794680844669637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6255738921571631171571397 1172951047794680844669637)
                      ·
                        rfl

theorem cell23_2284314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_2284314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284314 prefixEnd_2284314 := by exact prefixLift 2284314
  have htrace : WordTrace (prefixWord ++ tailWord_2284314) baseStart_2284314 baseEnd_2284314 := by
    simpa [prefixWord, tailWord_2284314, baseEnd_2284314] using wordTrace_append hprefix tailTrace_2284314
  have hstable : (prefixWord ++ tailWord_2284314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284314).length < 2 ^ (prefixWord ++ tailWord_2284314).sum := by decide
  have hdescent : baseEnd_2284314 < baseStart_2284314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284321 : List Nat := [1, 2, 3, 2, 1, 2, 3, 3, 1, 2, 3]
def baseStart_2284321 : Nat := 118140960795 + 2284321 * 2 ^ 59
def prefixEnd_2284321 : Nat := 4983230072969 + 3 ^ 40 * 2284321 * 2
def baseEnd_2284321 : Nat := 1172954642159262317282105

theorem tailTrace_2284321 : CollatzResearch.WordTrace tailWord_2284321 prefixEnd_2284321 1172954642159262317282105 := by
  unfold tailWord_2284321
  simp only [CollatzResearch.WordTrace]
  refine ⟨83316031557302622811996817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55544021038201748541331211 83316031557302622811996817)
  ·
    refine ⟨62487023667976967108997613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83316031557302622811996817 62487023667976967108997613)
    ·
      refine ⟨23432633875491362665874105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62487023667976967108997613 23432633875491362665874105)
      ·
        refine ⟨17574475406618521999405579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23432633875491362665874105 17574475406618521999405579)
        ·
          refine ⟨26361713109927782999108369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17574475406618521999405579 26361713109927782999108369)
          ·
            refine ⟨19771284832445837249331277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26361713109927782999108369 19771284832445837249331277)
            ·
              refine ⟨7414231812167188968499229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19771284832445837249331277 7414231812167188968499229)
              ·
                refine ⟨2780336929562695863187211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7414231812167188968499229 2780336929562695863187211)
                ·
                  refine ⟨4170505394344043794780817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2780336929562695863187211 4170505394344043794780817)
                  ·
                    refine ⟨3127879045758032846085613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4170505394344043794780817 3127879045758032846085613)
                    ·
                      refine ⟨1172954642159262317282105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3127879045758032846085613 1172954642159262317282105)
                      ·
                        rfl

theorem cell23_2284321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_2284321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284321 prefixEnd_2284321 := by exact prefixLift 2284321
  have htrace : WordTrace (prefixWord ++ tailWord_2284321) baseStart_2284321 baseEnd_2284321 := by
    simpa [prefixWord, tailWord_2284321, baseEnd_2284321] using wordTrace_append hprefix tailTrace_2284321
  have hstable : (prefixWord ++ tailWord_2284321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284321).length < 2 ^ (prefixWord ++ tailWord_2284321).sum := by decide
  have hdescent : baseEnd_2284321 < baseStart_2284321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284324 : List Nat := [2, 3, 1, 3, 3, 1, 10]
def baseStart_2284324 : Nat := 118140960795 + 2284324 * 2 ^ 59
def prefixEnd_2284324 : Nat := 4983230072969 + 3 ^ 40 * 2284324 * 2
def baseEnd_2284324 : Nat := 14480940525941059327711

theorem tailTrace_2284324 : CollatzResearch.WordTrace tailWord_2284324 prefixEnd_2284324 14480940525941059327711 := by
  unfold tailWord_2284324
  simp only [CollatzResearch.WordTrace]
  refine ⟨41658070488145877162178013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55544093984194502882904017 41658070488145877162178013)
  ·
    refine ⟨15621776433054703935816755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41658070488145877162178013 15621776433054703935816755)
    ·
      refine ⟨23432664649582055903725133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15621776433054703935816755 23432664649582055903725133)
      ·
        refine ⟨8787249243593270963896925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23432664649582055903725133 8787249243593270963896925)
        ·
          refine ⟨3295218466347476611461347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8787249243593270963896925 3295218466347476611461347)
          ·
            refine ⟨4942827699521214917192021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3295218466347476611461347 4942827699521214917192021)
            ·
              refine ⟨14480940525941059327711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4942827699521214917192021 14480940525941059327711)
              ·
                rfl

theorem cell23_2284324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 10].length) (baseStart_2284324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284324 prefixEnd_2284324 := by exact prefixLift 2284324
  have htrace : WordTrace (prefixWord ++ tailWord_2284324) baseStart_2284324 baseEnd_2284324 := by
    simpa [prefixWord, tailWord_2284324, baseEnd_2284324] using wordTrace_append hprefix tailTrace_2284324
  have hstable : (prefixWord ++ tailWord_2284324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284324).length < 2 ^ (prefixWord ++ tailWord_2284324).sum := by decide
  have hdescent : baseEnd_2284324 < baseStart_2284324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284351 : List Nat := [1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 3]
def baseStart_2284351 : Nat := 118140960795 + 2284351 * 2 ^ 59
def prefixEnd_2284351 : Nat := 4983230072969 + 3 ^ 40 * 2284351 * 2
def baseEnd_2284351 : Nat := 1172970046578897199906967

theorem tailTrace_2284351 : CollatzResearch.WordTrace tailWord_2284351 prefixEnd_2284351 1172970046578897199906967 := by
  unfold tailWord_2284351
  simp only [CollatzResearch.WordTrace]
  refine ⟨83317125747193937935588907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55544750498129291957059271 83317125747193937935588907)
  ·
    refine ⟨124975688620790906903383361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83317125747193937935588907 124975688620790906903383361)
    ·
      refine ⟨93731766465593180177537521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124975688620790906903383361 93731766465593180177537521)
      ·
        refine ⟨70298824849194885133153141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93731766465593180177537521 70298824849194885133153141)
        ·
          refine ⟨6590514829612020481233107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70298824849194885133153141 6590514829612020481233107)
          ·
            refine ⟨9885772244418030721849661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6590514829612020481233107 9885772244418030721849661)
            ·
              refine ⟨3707164591656761520693623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9885772244418030721849661 3707164591656761520693623)
              ·
                refine ⟨5560746887485142281040435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3707164591656761520693623 5560746887485142281040435)
                ·
                  refine ⟨8341120331227713421560653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5560746887485142281040435 8341120331227713421560653)
                  ·
                    refine ⟨3127920124210392533085245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8341120331227713421560653 3127920124210392533085245)
                    ·
                      refine ⟨1172970046578897199906967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3127920124210392533085245 1172970046578897199906967)
                      ·
                        rfl

theorem cell23_2284351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_2284351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284351 prefixEnd_2284351 := by exact prefixLift 2284351
  have htrace : WordTrace (prefixWord ++ tailWord_2284351) baseStart_2284351 baseEnd_2284351 := by
    simpa [prefixWord, tailWord_2284351, baseEnd_2284351] using wordTrace_append hprefix tailTrace_2284351
  have hstable : (prefixWord ++ tailWord_2284351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284351).length < 2 ^ (prefixWord ++ tailWord_2284351).sum := by decide
  have hdescent : baseEnd_2284351 < baseStart_2284351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284357 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 8]
def baseStart_2284357 : Nat := 118140960795 + 2284357 * 2 ^ 59
def prefixEnd_2284357 : Nat := 4983230072969 + 3 ^ 40 * 2284357 * 2
def baseEnd_2284357 : Nat := 1172973127462824176431939

theorem tailTrace_2284357 : CollatzResearch.WordTrace tailWord_2284357 prefixEnd_2284357 1172973127462824176431939 := by
  unfold tailWord_2284357
  simp only [CollatzResearch.WordTrace]
  refine ⟨83317344585172200960307325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55544896390114800640204883 83317344585172200960307325)
  ·
    refine ⟨31244004219439575360115247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83317344585172200960307325 31244004219439575360115247)
    ·
      refine ⟨46866006329159363040172871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31244004219439575360115247 46866006329159363040172871)
      ·
        refine ⟨70299009493739044560259307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46866006329159363040172871 70299009493739044560259307)
        ·
          refine ⟨105448514240608566840388961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70299009493739044560259307 105448514240608566840388961)
          ·
            refine ⟨79086385680456425130291721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105448514240608566840388961 79086385680456425130291721)
            ·
              refine ⟨59314789260342318847718791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79086385680456425130291721 59314789260342318847718791)
              ·
                refine ⟨88972183890513478271578187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59314789260342318847718791 88972183890513478271578187)
                ·
                  refine ⟨133458275835770217407367281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88972183890513478271578187 133458275835770217407367281)
                  ·
                    refine ⟨100093706876827663055525461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 133458275835770217407367281 100093706876827663055525461)
                    ·
                      refine ⟨1172973127462824176431939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 100093706876827663055525461 1172973127462824176431939)
                      ·
                        rfl

theorem cell23_2284357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_2284357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284357 prefixEnd_2284357 := by exact prefixLift 2284357
  have htrace : WordTrace (prefixWord ++ tailWord_2284357) baseStart_2284357 baseEnd_2284357 := by
    simpa [prefixWord, tailWord_2284357, baseEnd_2284357] using wordTrace_append hprefix tailTrace_2284357
  have hstable : (prefixWord ++ tailWord_2284357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284357).length < 2 ^ (prefixWord ++ tailWord_2284357).sum := by decide
  have hdescent : baseEnd_2284357 < baseStart_2284357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284358 : List Nat := [6, 1, 1, 2, 2, 1, 1, 9]
def baseStart_2284358 : Nat := 118140960795 + 2284358 * 2 ^ 59
def prefixEnd_2284358 : Nat := 4983230072969 + 3 ^ 40 * 2284358 * 2
def baseEnd_2284358 : Nat := 43443468183091802685905

theorem tailTrace_2284358 : CollatzResearch.WordTrace tailWord_2284358 prefixEnd_2284358 43443468183091802685905 := by
  unfold tailWord_2284358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2603668158067768066596679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55544920705445718754062485 2603668158067768066596679)
  ·
    refine ⟨3905502237101652099895019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2603668158067768066596679 3905502237101652099895019)
    ·
      refine ⟨5858253355652478149842529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3905502237101652099895019 5858253355652478149842529)
      ·
        refine ⟨4393690016739358612381897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5858253355652478149842529 4393690016739358612381897)
        ·
          refine ⟨3295267512554518959286423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4393690016739358612381897 3295267512554518959286423)
          ·
            refine ⟨4942901268831778438929635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3295267512554518959286423 4942901268831778438929635)
            ·
              refine ⟨7414351903247667658394453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4942901268831778438929635 7414351903247667658394453)
              ·
                refine ⟨43443468183091802685905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7414351903247667658394453 43443468183091802685905)
                ·
                  rfl

theorem cell23_2284358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_2284358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284358 prefixEnd_2284358 := by exact prefixLift 2284358
  have htrace : WordTrace (prefixWord ++ tailWord_2284358) baseStart_2284358 baseEnd_2284358 := by
    simpa [prefixWord, tailWord_2284358, baseEnd_2284358] using wordTrace_append hprefix tailTrace_2284358
  have hstable : (prefixWord ++ tailWord_2284358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284358).length < 2 ^ (prefixWord ++ tailWord_2284358).sum := by decide
  have hdescent : baseEnd_2284358 < baseStart_2284358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284364 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 2, 2, 5]
def baseStart_2284364 : Nat := 118140960795 + 2284364 * 2 ^ 59
def prefixEnd_2284364 : Nat := 4983230072969 + 3 ^ 40 * 2284364 * 2
def baseEnd_2284364 : Nat := 1172976721827405649044407

theorem tailTrace_2284364 : CollatzResearch.WordTrace tailWord_2284364 prefixEnd_2284364 1172976721827405649044407 := by
  unfold tailWord_2284364
  simp only [CollatzResearch.WordTrace]
  refine ⟨41658799948073420577906073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55545066597431227437208097 41658799948073420577906073)
  ·
    refine ⟨31244099961055065433429555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41658799948073420577906073 31244099961055065433429555)
    ·
      refine ⟨46866149941582598150144333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31244099961055065433429555 46866149941582598150144333)
      ·
        refine ⟨17574806228093474306304125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46866149941582598150144333 17574806228093474306304125)
        ·
          refine ⟨6590552335535052864864047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17574806228093474306304125 6590552335535052864864047)
          ·
            refine ⟨9885828503302579297296071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6590552335535052864864047 9885828503302579297296071)
            ·
              refine ⟨14828742754953868945944107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9885828503302579297296071 14828742754953868945944107)
              ·
                refine ⟨22243114132430803418916161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14828742754953868945944107 22243114132430803418916161)
                ·
                  refine ⟨16682335599323102564187121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22243114132430803418916161 16682335599323102564187121)
                  ·
                    refine ⟨12511751699492326923140341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16682335599323102564187121 12511751699492326923140341)
                    ·
                      refine ⟨1172976721827405649044407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12511751699492326923140341 1172976721827405649044407)
                      ·
                        rfl

theorem cell23_2284364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_2284364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284364 prefixEnd_2284364 := by exact prefixLift 2284364
  have htrace : WordTrace (prefixWord ++ tailWord_2284364) baseStart_2284364 baseEnd_2284364 := by
    simpa [prefixWord, tailWord_2284364, baseEnd_2284364] using wordTrace_append hprefix tailTrace_2284364
  have hstable : (prefixWord ++ tailWord_2284364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284364).length < 2 ^ (prefixWord ++ tailWord_2284364).sum := by decide
  have hdescent : baseEnd_2284364 < baseStart_2284364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284369 : List Nat := [1, 2, 2, 1, 7, 1, 1, 3, 1, 2, 2]
def baseStart_2284369 : Nat := 118140960795 + 2284369 * 2 ^ 59
def prefixEnd_2284369 : Nat := 4983230072969 + 3 ^ 40 * 2284369 * 2
def baseEnd_2284369 : Nat := 1172979289230678129481885

theorem tailTrace_2284369 : CollatzResearch.WordTrace tailWord_2284369 prefixEnd_2284369 1172979289230678129481885 := by
  unfold tailWord_2284369
  simp only [CollatzResearch.WordTrace]
  refine ⟨83317782261128727009744161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55545188174085818006496107 83317782261128727009744161)
  ·
    refine ⟨62488336695846545257308121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83317782261128727009744161 62488336695846545257308121)
    ·
      refine ⟨46866252521884908942981091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62488336695846545257308121 46866252521884908942981091)
      ·
        refine ⟨70299378782827363414471637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46866252521884908942981091 70299378782827363414471637)
        ·
          refine ⟨1647641690222516330026679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 70299378782827363414471637 1647641690222516330026679)
          ·
            refine ⟨2471462535333774495040019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1647641690222516330026679 2471462535333774495040019)
            ·
              refine ⟨3707193803000661742560029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2471462535333774495040019 3707193803000661742560029)
              ·
                refine ⟨1390197676125248153460011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3707193803000661742560029 1390197676125248153460011)
                ·
                  refine ⟨2085296514187872230190017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1390197676125248153460011 2085296514187872230190017)
                  ·
                    refine ⟨1563972385640904172642513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2085296514187872230190017 1563972385640904172642513)
                    ·
                      refine ⟨1172979289230678129481885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1563972385640904172642513 1172979289230678129481885)
                      ·
                        rfl

theorem cell23_2284369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 1, 2, 2].length) (baseStart_2284369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284369 prefixEnd_2284369 := by exact prefixLift 2284369
  have htrace : WordTrace (prefixWord ++ tailWord_2284369) baseStart_2284369 baseEnd_2284369 := by
    simpa [prefixWord, tailWord_2284369, baseEnd_2284369] using wordTrace_append hprefix tailTrace_2284369
  have hstable : (prefixWord ++ tailWord_2284369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284369).length < 2 ^ (prefixWord ++ tailWord_2284369).sum := by decide
  have hdescent : baseEnd_2284369 < baseStart_2284369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284378 : List Nat := [3, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2]
def baseStart_2284378 : Nat := 118140960795 + 2284378 * 2 ^ 59
def prefixEnd_2284378 : Nat := 4983230072969 + 3 ^ 40 * 2284378 * 2
def baseEnd_2284378 : Nat := 1172983910556568594269343

theorem tailTrace_2284378 : CollatzResearch.WordTrace tailWord_2284378 prefixEnd_2284378 1172983910556568594269343 := by
  unfold tailWord_2284378
  simp only [CollatzResearch.WordTrace]
  refine ⟨20829527629524030386705447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55545407012064081031214525 20829527629524030386705447)
  ·
    refine ⟨31244291444286045580058171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20829527629524030386705447 31244291444286045580058171)
    ·
      refine ⟨46866437166429068370087257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31244291444286045580058171 46866437166429068370087257)
      ·
        refine ⟨35149827874821801277565443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46866437166429068370087257 35149827874821801277565443)
        ·
          refine ⟨52724741812232701916348165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35149827874821801277565443 52724741812232701916348165)
          ·
            refine ⟨9885889089793631609315281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52724741812232701916348165 9885889089793631609315281)
            ·
              refine ⟨7414416817345223706986461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9885889089793631609315281 7414416817345223706986461)
              ·
                refine ⟨2780406306504458890119923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7414416817345223706986461 2780406306504458890119923)
                ·
                  refine ⟨4170609459756688335179885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2780406306504458890119923 4170609459756688335179885)
                  ·
                    refine ⟨1563978547408758125692457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4170609459756688335179885 1563978547408758125692457)
                    ·
                      refine ⟨1172983910556568594269343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1563978547408758125692457 1172983910556568594269343)
                      ·
                        rfl

theorem cell23_2284378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_2284378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284378 prefixEnd_2284378 := by exact prefixLift 2284378
  have htrace : WordTrace (prefixWord ++ tailWord_2284378) baseStart_2284378 baseEnd_2284378 := by
    simpa [prefixWord, tailWord_2284378, baseEnd_2284378] using wordTrace_append hprefix tailTrace_2284378
  have hstable : (prefixWord ++ tailWord_2284378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284378).length < 2 ^ (prefixWord ++ tailWord_2284378).sum := by decide
  have hdescent : baseEnd_2284378 < baseStart_2284378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284442 : List Nat := [3, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2]
def baseStart_2284442 : Nat := 118140960795 + 2284442 * 2 ^ 59
def prefixEnd_2284442 : Nat := 4983230072969 + 3 ^ 40 * 2284442 * 2
def baseEnd_2284442 : Nat := 1173016773318456343869049

theorem tailTrace_2284442 : CollatzResearch.WordTrace tailWord_2284442 prefixEnd_2284442 1173016773318456343869049 := by
  unfold tailWord_2284442
  simp only [CollatzResearch.WordTrace]
  refine ⟨20830111197466065119287895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55546963193242840318101053 20830111197466065119287895)
  ·
    refine ⟨31245166796199097678931843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20830111197466065119287895 31245166796199097678931843)
    ·
      refine ⟨46867750194298646518397765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31245166796199097678931843 46867750194298646518397765)
      ·
        refine ⟨8787703161430996222199581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46867750194298646518397765 8787703161430996222199581)
        ·
          refine ⟨3295388685536623583324843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8787703161430996222199581 3295388685536623583324843)
          ·
            refine ⟨4943083028304935374987265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3295388685536623583324843 4943083028304935374987265)
            ·
              refine ⟨3707312271228701531240449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4943083028304935374987265 3707312271228701531240449)
              ·
                refine ⟨2780484203421526148430337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3707312271228701531240449 2780484203421526148430337)
                ·
                  refine ⟨2085363152566144611322753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2780484203421526148430337 2085363152566144611322753)
                  ·
                    refine ⟨1564022364424608458492065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2085363152566144611322753 1564022364424608458492065)
                    ·
                      refine ⟨1173016773318456343869049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1564022364424608458492065 1173016773318456343869049)
                      ·
                        rfl

theorem cell23_2284442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_2284442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284442 prefixEnd_2284442 := by exact prefixLift 2284442
  have htrace : WordTrace (prefixWord ++ tailWord_2284442) baseStart_2284442 baseEnd_2284442 := by
    simpa [prefixWord, tailWord_2284442, baseEnd_2284442] using wordTrace_append hprefix tailTrace_2284442
  have hstable : (prefixWord ++ tailWord_2284442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284442).length < 2 ^ (prefixWord ++ tailWord_2284442).sum := by decide
  have hdescent : baseEnd_2284442 < baseStart_2284442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284448 : List Nat := [2, 1, 1, 4, 1, 1, 6, 2, 5]
def baseStart_2284448 : Nat := 118140960795 + 2284448 * 2 ^ 59
def prefixEnd_2284448 : Nat := 4983230072969 + 3 ^ 40 * 2284448 * 2
def baseEnd_2284448 : Nat := 130335539355820368932669

theorem tailTrace_2284448 : CollatzResearch.WordTrace tailWord_2284448 prefixEnd_2284448 130335539355820368932669 := by
  unfold tailWord_2284448
  simp only [CollatzResearch.WordTrace]
  refine ⟨41660331813921261750934999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55547109085228349001246665 41660331813921261750934999)
  ·
    refine ⟨62490497720881892626402499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41660331813921261750934999 62490497720881892626402499)
    ·
      refine ⟨93735746581322838939603749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62490497720881892626402499 93735746581322838939603749)
      ·
        refine ⟨17575452483998032301175703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93735746581322838939603749 17575452483998032301175703)
        ·
          refine ⟨26363178725997048451763555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17575452483998032301175703 26363178725997048451763555)
          ·
            refine ⟨39544768088995572677645333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26363178725997048451763555 39544768088995572677645333)
            ·
              refine ⟨1853661004171667469264625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39544768088995572677645333 1853661004171667469264625)
              ·
                refine ⟨1390245753128750601948469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1853661004171667469264625 1390245753128750601948469)
                ·
                  refine ⟨130335539355820368932669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1390245753128750601948469 130335539355820368932669)
                  ·
                    rfl

theorem cell23_2284448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 5].length) (baseStart_2284448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284448 prefixEnd_2284448 := by exact prefixLift 2284448
  have htrace : WordTrace (prefixWord ++ tailWord_2284448) baseStart_2284448 baseEnd_2284448 := by
    simpa [prefixWord, tailWord_2284448, baseEnd_2284448] using wordTrace_append hprefix tailTrace_2284448
  have hstable : (prefixWord ++ tailWord_2284448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284448).length < 2 ^ (prefixWord ++ tailWord_2284448).sum := by decide
  have hdescent : baseEnd_2284448 < baseStart_2284448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284451 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 2, 5, 2]
def baseStart_2284451 : Nat := 118140960795 + 2284451 * 2 ^ 59
def prefixEnd_2284451 : Nat := 4983230072969 + 3 ^ 40 * 2284451 * 2
def baseEnd_2284451 : Nat := 1173021394644346808656507

theorem tailTrace_2284451 : CollatzResearch.WordTrace tailWord_2284451 prefixEnd_2284451 1173021394644346808656507 := by
  unfold tailWord_2284451
  simp only [CollatzResearch.WordTrace]
  refine ⟨83320773046831655014229207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55547182031221103342819471 83320773046831655014229207)
  ·
    refine ⟨124981159570247482521343811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83320773046831655014229207 124981159570247482521343811)
    ·
      refine ⟨187471739355371223782015717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124981159570247482521343811 187471739355371223782015717)
      ·
        refine ⟨35150951129132104459127947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187471739355371223782015717 35150951129132104459127947)
        ·
          refine ⟨52726426693698156688691921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35150951129132104459127947 52726426693698156688691921)
          ·
            refine ⟨39544820020273617516518941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52726426693698156688691921 39544820020273617516518941)
            ·
              refine ⟨14829307507602606568694603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39544820020273617516518941 14829307507602606568694603)
              ·
                refine ⟨22243961261403909853041905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14829307507602606568694603 22243961261403909853041905)
                ·
                  refine ⟨16682970946052932389781429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22243961261403909853041905 16682970946052932389781429)
                  ·
                    refine ⟨1564028526192462411542009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16682970946052932389781429 1564028526192462411542009)
                    ·
                      refine ⟨1173021394644346808656507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1564028526192462411542009 1173021394644346808656507)
                      ·
                        rfl

theorem cell23_2284451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_2284451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284451 prefixEnd_2284451 := by exact prefixLift 2284451
  have htrace : WordTrace (prefixWord ++ tailWord_2284451) baseStart_2284451 baseEnd_2284451 := by
    simpa [prefixWord, tailWord_2284451, baseEnd_2284451] using wordTrace_append hprefix tailTrace_2284451
  have hstable : (prefixWord ++ tailWord_2284451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284451).length < 2 ^ (prefixWord ++ tailWord_2284451).sum := by decide
  have hdescent : baseEnd_2284451 < baseStart_2284451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284493 : List Nat := [1, 6, 3, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_2284493 : Nat := 118140960795 + 2284493 * 2 ^ 59
def prefixEnd_2284493 : Nat := 4983230072969 + 3 ^ 40 * 2284493 * 2
def baseEnd_2284493 : Nat := 1173042960831835644331315

theorem tailTrace_2284493 : CollatzResearch.WordTrace tailWord_2284493 prefixEnd_2284493 1173042960831835644331315 := by
  unfold tailWord_2284493
  simp only [CollatzResearch.WordTrace]
  refine ⟨83322304912679496187258133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55548203275119664124838755 83322304912679496187258133)
  ·
    refine ⟨3905733042781851383777725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 83322304912679496187258133 3905733042781851383777725)
    ·
      refine ⟨1464649891043194268916647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3905733042781851383777725 1464649891043194268916647)
      ·
        refine ⟨2196974836564791403374971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1464649891043194268916647 2196974836564791403374971)
        ·
          refine ⟨3295462254847187105062457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2196974836564791403374971 3295462254847187105062457)
          ·
            refine ⟨2471596691135390328796843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3295462254847187105062457 2471596691135390328796843)
            ·
              refine ⟨3707395036703085493195265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2471596691135390328796843 3707395036703085493195265)
              ·
                refine ⟨2780546277527314119896449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3707395036703085493195265 2780546277527314119896449)
                ·
                  refine ⟨2085409708145485589922337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2780546277527314119896449 2085409708145485589922337)
                  ·
                    refine ⟨1564057281109114192441753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2085409708145485589922337 1564057281109114192441753)
                    ·
                      refine ⟨1173042960831835644331315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1564057281109114192441753 1173042960831835644331315)
                      ·
                        rfl

theorem cell23_2284493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_2284493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284493 prefixEnd_2284493 := by exact prefixLift 2284493
  have htrace : WordTrace (prefixWord ++ tailWord_2284493) baseStart_2284493 baseEnd_2284493 := by
    simpa [prefixWord, tailWord_2284493, baseEnd_2284493] using wordTrace_append hprefix tailTrace_2284493
  have hstable : (prefixWord ++ tailWord_2284493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284493).length < 2 ^ (prefixWord ++ tailWord_2284493).sum := by decide
  have hdescent : baseEnd_2284493 < baseStart_2284493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284544 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 7]
def baseStart_2284544 : Nat := 118140960795 + 2284544 * 2 ^ 59
def prefixEnd_2284544 : Nat := 4983230072969 + 3 ^ 40 * 2284544 * 2
def baseEnd_2284544 : Nat := 1173069148345214944793579

theorem tailTrace_2284544 : CollatzResearch.WordTrace tailWord_2284544 prefixEnd_2284544 1173069148345214944793579 := by
  unfold tailWord_2284544
  simp only [CollatzResearch.WordTrace]
  refine ⟨41662082517747365948682343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55549443356996487931576457 41662082517747365948682343)
  ·
    refine ⟨62493123776621048923023515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41662082517747365948682343 62493123776621048923023515)
    ·
      refine ⟨93739685664931573384535273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62493123776621048923023515 93739685664931573384535273)
      ·
        refine ⟨70304764248698680038401455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93739685664931573384535273 70304764248698680038401455)
        ·
          refine ⟨105457146373048020057602183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70304764248698680038401455 105457146373048020057602183)
          ·
            refine ⟨158185719559572030086403275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105457146373048020057602183 158185719559572030086403275)
            ·
              refine ⟨237278579339358045129604913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158185719559572030086403275 237278579339358045129604913)
              ·
                refine ⟨177958934504518533847203685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 237278579339358045129604913 177958934504518533847203685)
                ·
                  refine ⟨33367300219597225096350691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177958934504518533847203685 33367300219597225096350691)
                  ·
                    refine ⟨50050950329395837644526037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33367300219597225096350691 50050950329395837644526037)
                    ·
                      refine ⟨1173069148345214944793579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50050950329395837644526037 1173069148345214944793579)
                      ·
                        rfl

theorem cell23_2284544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_2284544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284544 prefixEnd_2284544 := by exact prefixLift 2284544
  have htrace : WordTrace (prefixWord ++ tailWord_2284544) baseStart_2284544 baseEnd_2284544 := by
    simpa [prefixWord, tailWord_2284544, baseEnd_2284544] using wordTrace_append hprefix tailTrace_2284544
  have hstable : (prefixWord ++ tailWord_2284544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284544).length < 2 ^ (prefixWord ++ tailWord_2284544).sum := by decide
  have hdescent : baseEnd_2284544 < baseStart_2284544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284565 : List Nat := [1, 3, 2, 1, 4, 1, 3, 1, 3, 1, 3]
def baseStart_2284565 : Nat := 118140960795 + 2284565 * 2 ^ 59
def prefixEnd_2284565 : Nat := 4983230072969 + 3 ^ 40 * 2284565 * 2
def baseEnd_2284565 : Nat := 1173079931438959362630983

theorem tailTrace_2284565 : CollatzResearch.WordTrace tailWord_2284565 prefixEnd_2284565 1173079931438959362630983 := by
  unfold tailWord_2284565
  simp only [CollatzResearch.WordTrace]
  refine ⟨83324930968418652483879149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55549953978945768322586099 83324930968418652483879149)
  ·
    refine ⟨31246849113156994681454681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83324930968418652483879149 31246849113156994681454681)
    ·
      refine ⟨23435136834867746011091011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31246849113156994681454681 23435136834867746011091011)
      ·
        refine ⟨35152705252301619016636517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23435136834867746011091011 35152705252301619016636517)
        ·
          refine ⟨6591132234806553565619347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35152705252301619016636517 6591132234806553565619347)
          ·
            refine ⟨9886698352209830348429021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6591132234806553565619347 9886698352209830348429021)
            ·
              refine ⟨3707511882078686380660883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9886698352209830348429021 3707511882078686380660883)
              ·
                refine ⟨5561267823118029570991325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3707511882078686380660883 5561267823118029570991325)
                ·
                  refine ⟨2085475433669261089121747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5561267823118029570991325 2085475433669261089121747)
                  ·
                    refine ⟨3128213150503891633682621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2085475433669261089121747 3128213150503891633682621)
                    ·
                      refine ⟨1173079931438959362630983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3128213150503891633682621 1173079931438959362630983)
                      ·
                        rfl

theorem cell23_2284565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_2284565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284565 prefixEnd_2284565 := by exact prefixLift 2284565
  have htrace : WordTrace (prefixWord ++ tailWord_2284565) baseStart_2284565 baseEnd_2284565 := by
    simpa [prefixWord, tailWord_2284565, baseEnd_2284565] using wordTrace_append hprefix tailTrace_2284565
  have hstable : (prefixWord ++ tailWord_2284565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284565).length < 2 ^ (prefixWord ++ tailWord_2284565).sum := by decide
  have hdescent : baseEnd_2284565 < baseStart_2284565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284572 : List Nat := [2, 2, 3, 1, 5, 1, 2, 1, 6]
def baseStart_2284572 : Nat := 118140960795 + 2284572 * 2 ^ 59
def prefixEnd_2284572 : Nat := 4983230072969 + 3 ^ 40 * 2284572 * 2
def baseEnd_2284572 : Nat := 130342613978171203915939

theorem tailTrace_2284572 : CollatzResearch.WordTrace tailWord_2284572 prefixEnd_2284572 130342613978171203915939 := by
  unfold tailWord_2284572
  simp only [CollatzResearch.WordTrace]
  refine ⟨41662593139696646339691985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55550124186262195119589313 41662593139696646339691985)
  ·
    refine ⟨31246944854772484754768989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41662593139696646339691985 31246944854772484754768989)
    ·
      refine ⟨11717604320539681783038371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31246944854772484754768989 11717604320539681783038371)
      ·
        refine ⟨17576406480809522674557557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11717604320539681783038371 17576406480809522674557557)
        ·
          refine ⟨1647788107575892750739771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17576406480809522674557557 1647788107575892750739771)
          ·
            refine ⟨2471682161363839126109657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1647788107575892750739771 2471682161363839126109657)
            ·
              refine ⟨1853761621022879344582243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2471682161363839126109657 1853761621022879344582243)
              ·
                refine ⟨2780642431534319016873365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1853761621022879344582243 2780642431534319016873365)
                ·
                  refine ⟨130342613978171203915939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2780642431534319016873365 130342613978171203915939)
                  ·
                    rfl

theorem cell23_2284572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 6].length) (baseStart_2284572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284572 prefixEnd_2284572 := by exact prefixLift 2284572
  have htrace : WordTrace (prefixWord ++ tailWord_2284572) baseStart_2284572 baseEnd_2284572 := by
    simpa [prefixWord, tailWord_2284572, baseEnd_2284572] using wordTrace_append hprefix tailTrace_2284572
  have hstable : (prefixWord ++ tailWord_2284572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284572).length < 2 ^ (prefixWord ++ tailWord_2284572).sum := by decide
  have hdescent : baseEnd_2284572 < baseStart_2284572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284581 : List Nat := [1, 3, 1, 2, 2, 2, 2, 3, 1, 6]
def baseStart_2284581 : Nat := 118140960795 + 2284581 * 2 ^ 59
def prefixEnd_2284581 : Nat := 4983230072969 + 3 ^ 40 * 2284581 * 2
def baseEnd_2284581 : Nat := 391029382376477100010303

theorem tailTrace_2284581 : CollatzResearch.WordTrace tailWord_2284581 prefixEnd_2284581 391029382376477100010303 := by
  unfold tailWord_2284581
  simp only [CollatzResearch.WordTrace]
  refine ⟨83325514536360687216461597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55550343024240458144307731 83325514536360687216461597)
  ·
    refine ⟨31247067951135257706173099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83325514536360687216461597 31247067951135257706173099)
    ·
      refine ⟨46870601926702886559259649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31247067951135257706173099 46870601926702886559259649)
      ·
        refine ⟨35152951445027164919444737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46870601926702886559259649 35152951445027164919444737)
        ·
          refine ⟨26364713583770373689583553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35152951445027164919444737 26364713583770373689583553)
          ·
            refine ⟨19773535187827780267187665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26364713583770373689583553 19773535187827780267187665)
            ·
              refine ⟨14830151390870835200390749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19773535187827780267187665 14830151390870835200390749)
              ·
                refine ⟨5561306771576563200146531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14830151390870835200390749 5561306771576563200146531)
                ·
                  refine ⟨8341960157364844800219797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5561306771576563200146531 8341960157364844800219797)
                  ·
                    refine ⟨391029382376477100010303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8341960157364844800219797 391029382376477100010303)
                    ·
                      rfl

theorem cell23_2284581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_2284581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284581 prefixEnd_2284581 := by exact prefixLift 2284581
  have htrace : WordTrace (prefixWord ++ tailWord_2284581) baseStart_2284581 baseEnd_2284581 := by
    simpa [prefixWord, tailWord_2284581, baseEnd_2284581] using wordTrace_append hprefix tailTrace_2284581
  have hstable : (prefixWord ++ tailWord_2284581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284581).length < 2 ^ (prefixWord ++ tailWord_2284581).sum := by decide
  have hdescent : baseEnd_2284581 < baseStart_2284581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284598 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_2284598 : Nat := 118140960795 + 2284598 * 2 ^ 59
def prefixEnd_2284598 : Nat := 4983230072969 + 3 ^ 40 * 2284598 * 2
def baseEnd_2284598 : Nat := 391032292100185911172777

theorem tailTrace_2284598 : CollatzResearch.WordTrace tailWord_2284598 prefixEnd_2284598 391032292100185911172777 := by
  unfold tailWord_2284598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5207883411081193694989403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55550756384866066079886965 5207883411081193694989403)
  ·
    refine ⟨7811825116621790542484105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5207883411081193694989403 7811825116621790542484105)
    ·
      refine ⟨5858868837466342906863079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7811825116621790542484105 5858868837466342906863079)
      ·
        refine ⟨8788303256199514360294619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5858868837466342906863079 8788303256199514360294619)
        ·
          refine ⟨13182454884299271540441929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8788303256199514360294619 13182454884299271540441929)
          ·
            refine ⟨9886841163224453655331447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13182454884299271540441929 9886841163224453655331447)
            ·
              refine ⟨14830261744836680482997171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9886841163224453655331447 14830261744836680482997171)
              ·
                refine ⟨22245392617255020724495757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14830261744836680482997171 22245392617255020724495757)
                ·
                  refine ⟨8342022231470632771685909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22245392617255020724495757 8342022231470632771685909)
                  ·
                    refine ⟨391032292100185911172777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8342022231470632771685909 391032292100185911172777)
                    ·
                      rfl

theorem cell23_2284598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_2284598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284598 prefixEnd_2284598 := by exact prefixLift 2284598
  have htrace : WordTrace (prefixWord ++ tailWord_2284598) baseStart_2284598 baseEnd_2284598 := by
    simpa [prefixWord, tailWord_2284598, baseEnd_2284598] using wordTrace_append hprefix tailTrace_2284598
  have hstable : (prefixWord ++ tailWord_2284598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284598).length < 2 ^ (prefixWord ++ tailWord_2284598).sum := by decide
  have hdescent : baseEnd_2284598 < baseStart_2284598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284615 : List Nat := [1, 1, 4, 1, 3, 3, 2, 2, 2, 4]
def baseStart_2284615 : Nat := 118140960795 + 2284615 * 2 ^ 59
def prefixEnd_2284615 : Nat := 4983230072969 + 3 ^ 40 * 2284615 * 2
def baseEnd_2284615 : Nat := 391035201823894722335251

theorem tailTrace_2284615 : CollatzResearch.WordTrace tailWord_2284615 prefixEnd_2284615 391035201823894722335251 := by
  unfold tailWord_2284615
  simp only [CollatzResearch.WordTrace]
  refine ⟨83326754618237511023199299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55551169745491674015466199 83326754618237511023199299)
  ·
    refine ⟨124990131927356266534798949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83326754618237511023199299 124990131927356266534798949)
    ·
      refine ⟨23435649736379299975274803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124990131927356266534798949 23435649736379299975274803)
      ·
        refine ⟨35153474604568949962912205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23435649736379299975274803 35153474604568949962912205)
        ·
          refine ⟨13182552976713356236092077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35153474604568949962912205 13182552976713356236092077)
          ·
            refine ⟨4943457366267508588534529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13182552976713356236092077 4943457366267508588534529)
            ·
              refine ⟨3707593024700631441400897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4943457366267508588534529 3707593024700631441400897)
              ·
                refine ⟨2780694768525473581050673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3707593024700631441400897 2780694768525473581050673)
                ·
                  refine ⟨2085521076394105185788005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2780694768525473581050673 2085521076394105185788005)
                  ·
                    refine ⟨391035201823894722335251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2085521076394105185788005 391035201823894722335251)
                    ·
                      rfl

theorem cell23_2284615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_2284615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284615 prefixEnd_2284615 := by exact prefixLift 2284615
  have htrace : WordTrace (prefixWord ++ tailWord_2284615) baseStart_2284615 baseEnd_2284615 := by
    simpa [prefixWord, tailWord_2284615, baseEnd_2284615] using wordTrace_append hprefix tailTrace_2284615
  have hstable : (prefixWord ++ tailWord_2284615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284615).length < 2 ^ (prefixWord ++ tailWord_2284615).sum := by decide
  have hdescent : baseEnd_2284615 < baseStart_2284615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284728 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 2, 3, 3]
def baseStart_2284728 : Nat := 118140960795 + 2284728 * 2 ^ 59
def prefixEnd_2284728 : Nat := 4983230072969 + 3 ^ 40 * 2284728 * 2
def baseEnd_2284728 : Nat := 1173163628785642224892733

theorem tailTrace_2284728 : CollatzResearch.WordTrace tailWord_2284728 prefixEnd_2284728 1173163628785642224892733 := by
  unfold tailWord_2284728
  simp only [CollatzResearch.WordTrace]
  refine ⟨41665438033414065661031419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55553917377885420881375225 41665438033414065661031419)
  ·
    refine ⟨62498157050121098491547129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41665438033414065661031419 62498157050121098491547129)
    ·
      refine ⟨46873617787590823868660347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62498157050121098491547129 46873617787590823868660347)
      ·
        refine ⟨70310426681386235802990521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46873617787590823868660347 70310426681386235802990521)
        ·
          refine ⟨52732820011039676852242891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70310426681386235802990521 52732820011039676852242891)
          ·
            refine ⟨79099230016559515278364337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52732820011039676852242891 79099230016559515278364337)
            ·
              refine ⟨59324422512419636458773253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79099230016559515278364337 59324422512419636458773253)
              ·
                refine ⟨11123329221078681836019985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59324422512419636458773253 11123329221078681836019985)
                ·
                  refine ⟨8342496915809011377014989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11123329221078681836019985 8342496915809011377014989)
                  ·
                    refine ⟨3128436343428379266380621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8342496915809011377014989 3128436343428379266380621)
                    ·
                      refine ⟨1173163628785642224892733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3128436343428379266380621 1173163628785642224892733)
                      ·
                        rfl

theorem cell23_2284728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_2284728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284728 prefixEnd_2284728 := by exact prefixLift 2284728
  have htrace : WordTrace (prefixWord ++ tailWord_2284728) baseStart_2284728 baseEnd_2284728 := by
    simpa [prefixWord, tailWord_2284728, baseEnd_2284728] using wordTrace_append hprefix tailTrace_2284728
  have hstable : (prefixWord ++ tailWord_2284728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284728).length < 2 ^ (prefixWord ++ tailWord_2284728).sum := by decide
  have hdescent : baseEnd_2284728 < baseStart_2284728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284731 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 3, 7]
def baseStart_2284731 : Nat := 118140960795 + 2284731 * 2 ^ 59
def prefixEnd_2284731 : Nat := 4983230072969 + 3 ^ 40 * 2284731 * 2
def baseEnd_2284731 : Nat := 391055056409201904385073

theorem tailTrace_2284731 : CollatzResearch.WordTrace tailWord_2284731 prefixEnd_2284731 391055056409201904385073 := by
  unfold tailWord_2284731
  simp only [CollatzResearch.WordTrace]
  refine ⟨83330985485817262834422047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55553990323878175222948031 83330985485817262834422047)
  ·
    refine ⟨124996478228725894251633071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83330985485817262834422047 124996478228725894251633071)
    ·
      refine ⟨187494717343088841377449607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124996478228725894251633071 187494717343088841377449607)
      ·
        refine ⟨281242076014633262066174411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187494717343088841377449607 281242076014633262066174411)
        ·
          refine ⟨421863114021949893099261617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281242076014633262066174411 421863114021949893099261617)
          ·
            refine ⟨316397335516462419824446213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 421863114021949893099261617 316397335516462419824446213)
            ·
              refine ⟨59324500409336703717083665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 316397335516462419824446213 59324500409336703717083665)
              ·
                refine ⟨44493375307002527787812749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59324500409336703717083665 44493375307002527787812749)
                ·
                  refine ⟨16685015740125947920429781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44493375307002527787812749 16685015740125947920429781)
                  ·
                    refine ⟨391055056409201904385073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16685015740125947920429781 391055056409201904385073)
                    ·
                      rfl

theorem cell23_2284731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 7].length) (baseStart_2284731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284731 prefixEnd_2284731 := by exact prefixLift 2284731
  have htrace : WordTrace (prefixWord ++ tailWord_2284731) baseStart_2284731 baseEnd_2284731 := by
    simpa [prefixWord, tailWord_2284731, baseEnd_2284731] using wordTrace_append hprefix tailTrace_2284731
  have hstable : (prefixWord ++ tailWord_2284731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284731).length < 2 ^ (prefixWord ++ tailWord_2284731).sum := by decide
  have hdescent : baseEnd_2284731 < baseStart_2284731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284746 : List Nat := [3, 1, 2, 1, 3, 4, 2, 1, 2, 2, 2]
def baseStart_2284746 : Nat := 118140960795 + 2284746 * 2 ^ 59
def prefixEnd_2284746 : Nat := 4983230072969 + 3 ^ 40 * 2284746 * 2
def baseEnd_2284746 : Nat := 1173172871437423154467651

theorem tailTrace_2284746 : CollatzResearch.WordTrace tailWord_2284746 prefixEnd_2284746 1173172871437423154467651 := by
  unfold tailWord_2284746
  simp only [CollatzResearch.WordTrace]
  refine ⟨20832883145190730099054523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55554355053841946930812061 20832883145190730099054523)
  ·
    refine ⟨31249324717786095148581785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20832883145190730099054523 31249324717786095148581785)
    ·
      refine ⟨23436993538339571361436339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31249324717786095148581785 23436993538339571361436339)
      ·
        refine ⟨35155490307509357042154509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23436993538339571361436339 35155490307509357042154509)
        ·
          refine ⟨13183308865316008890807941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35155490307509357042154509 13183308865316008890807941)
          ·
            refine ⟨2471870412246751667026489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13183308865316008890807941 2471870412246751667026489)
            ·
              refine ⟨1853902809185063750269867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2471870412246751667026489 1853902809185063750269867)
              ·
                refine ⟨2780854213777595625404801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1853902809185063750269867 2780854213777595625404801)
                ·
                  refine ⟨2085640660333196719053601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2780854213777595625404801 2085640660333196719053601)
                  ·
                    refine ⟨1564230495249897539290201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2085640660333196719053601 1564230495249897539290201)
                    ·
                      refine ⟨1173172871437423154467651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1564230495249897539290201 1173172871437423154467651)
                      ·
                        rfl

theorem cell23_2284746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_2284746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284746 prefixEnd_2284746 := by exact prefixLift 2284746
  have htrace : WordTrace (prefixWord ++ tailWord_2284746) baseStart_2284746 baseEnd_2284746 := by
    simpa [prefixWord, tailWord_2284746, baseEnd_2284746] using wordTrace_append hprefix tailTrace_2284746
  have hstable : (prefixWord ++ tailWord_2284746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284746).length < 2 ^ (prefixWord ++ tailWord_2284746).sum := by decide
  have hdescent : baseEnd_2284746 < baseStart_2284746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284785 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 2, 4, 2]
def baseStart_2284785 : Nat := 118140960795 + 2284785 * 2 ^ 59
def prefixEnd_2284785 : Nat := 4983230072969 + 3 ^ 40 * 2284785 * 2
def baseEnd_2284785 : Nat := 1173192897182948501879971

theorem tailTrace_2284785 : CollatzResearch.WordTrace tailWord_2284785 prefixEnd_2284785 1173192897182948501879971 := by
  unfold tailWord_2284785
  simp only [CollatzResearch.WordTrace]
  refine ⟨83332955027621630056887809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55555303351747753371258539 83332955027621630056887809)
  ·
    refine ⟨62499716270716222542665857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83332955027621630056887809 62499716270716222542665857)
    ·
      refine ⟨46874787203037166906999393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62499716270716222542665857 46874787203037166906999393)
      ·
        refine ⟨35156090402277875180249545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46874787203037166906999393 35156090402277875180249545)
        ·
          refine ⟨26367067801708406385187159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35156090402277875180249545 26367067801708406385187159)
          ·
            refine ⟨39550601702562609577780739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26367067801708406385187159 39550601702562609577780739)
            ·
              refine ⟨59325902553843914366671109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39550601702562609577780739 59325902553843914366671109)
              ·
                refine ⟨11123606728845733943750833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59325902553843914366671109 11123606728845733943750833)
                ·
                  refine ⟨8342705046634300457813125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11123606728845733943750833 8342705046634300457813125)
                  ·
                    refine ⟨1564257196243931335839961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8342705046634300457813125 1564257196243931335839961)
                    ·
                      refine ⟨1173192897182948501879971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1564257196243931335839961 1173192897182948501879971)
                      ·
                        rfl

theorem cell23_2284785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_2284785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284785 prefixEnd_2284785 := by exact prefixLift 2284785
  have htrace : WordTrace (prefixWord ++ tailWord_2284785) baseStart_2284785 baseEnd_2284785 := by
    simpa [prefixWord, tailWord_2284785, baseEnd_2284785] using wordTrace_append hprefix tailTrace_2284785
  have hstable : (prefixWord ++ tailWord_2284785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284785).length < 2 ^ (prefixWord ++ tailWord_2284785).sum := by decide
  have hdescent : baseEnd_2284785 < baseStart_2284785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284786 : List Nat := [3, 2, 1, 3, 4, 1, 2, 2, 5]
def baseStart_2284786 : Nat := 118140960795 + 2284786 * 2 ^ 59
def prefixEnd_2284786 : Nat := 4983230072969 + 3 ^ 40 * 2284786 * 2
def baseEnd_2284786 : Nat := 130354823407066999774163

theorem tailTrace_2284786 : CollatzResearch.WordTrace tailWord_2284786 prefixEnd_2284786 130354823407066999774163 := by
  unfold tailWord_2284786
  simp only [CollatzResearch.WordTrace]
  refine ⟨20833247875154501806918553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55555327667078671485116141 20833247875154501806918553)
  ·
    refine ⟨15624935906365876355188915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20833247875154501806918553 15624935906365876355188915)
    ·
      refine ⟨23437403859548814532783373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15624935906365876355188915 23437403859548814532783373)
      ·
        refine ⟨8789026447330805449793765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23437403859548814532783373 8789026447330805449793765)
        ·
          refine ⟨1647942458874526021836331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8789026447330805449793765 1647942458874526021836331)
          ·
            refine ⟨2471913688311789032754497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1647942458874526021836331 2471913688311789032754497)
            ·
              refine ⟨1853935266233841774565873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2471913688311789032754497 1853935266233841774565873)
              ·
                refine ⟨1390451449675381330924405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1853935266233841774565873 1390451449675381330924405)
                ·
                  refine ⟨130354823407066999774163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1390451449675381330924405 130354823407066999774163)
                  ·
                    rfl

theorem cell23_2284786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_2284786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284786 prefixEnd_2284786 := by exact prefixLift 2284786
  have htrace : WordTrace (prefixWord ++ tailWord_2284786) baseStart_2284786 baseEnd_2284786 := by
    simpa [prefixWord, tailWord_2284786, baseEnd_2284786] using wordTrace_append hprefix tailTrace_2284786
  have hstable : (prefixWord ++ tailWord_2284786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284786).length < 2 ^ (prefixWord ++ tailWord_2284786).sum := by decide
  have hdescent : baseEnd_2284786 < baseStart_2284786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284829 : List Nat := [1, 4, 2, 3, 1, 1, 1, 5, 1, 4]
def baseStart_2284829 : Nat := 118140960795 + 2284829 * 2 ^ 59
def prefixEnd_2284829 : Nat := 4983230072969 + 3 ^ 40 * 2284829 * 2
def baseEnd_2284829 : Nat := 391071830110582109909923

theorem tailTrace_2284829 : CollatzResearch.WordTrace tailWord_2284829 prefixEnd_2284829 391071830110582109909923 := by
  unfold tailWord_2284829
  simp only [CollatzResearch.WordTrace]
  refine ⟨83334559839462225571489541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55556373226308150380993027 83334559839462225571489541)
  ·
    refine ⟨15625229969899167294654289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83334559839462225571489541 15625229969899167294654289)
    ·
      refine ⟨11718922477424375470990717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15625229969899167294654289 11718922477424375470990717)
      ·
        refine ⟨4394595929034140801621519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11718922477424375470990717 4394595929034140801621519)
        ·
          refine ⟨6591893893551211202432279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4394595929034140801621519 6591893893551211202432279)
          ·
            refine ⟨9887840840326816803648419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6591893893551211202432279 9887840840326816803648419)
            ·
              refine ⟨14831761260490225205472629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9887840840326816803648419 14831761260490225205472629)
              ·
                refine ⟨1390477618170958613013059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14831761260490225205472629 1390477618170958613013059)
                ·
                  refine ⟨2085716427256437919519589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1390477618170958613013059 2085716427256437919519589)
                  ·
                    refine ⟨391071830110582109909923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2085716427256437919519589 391071830110582109909923)
                    ·
                      rfl

theorem cell23_2284829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_2284829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284829 prefixEnd_2284829 := by exact prefixLift 2284829
  have htrace : WordTrace (prefixWord ++ tailWord_2284829) baseStart_2284829 baseEnd_2284829 := by
    simpa [prefixWord, tailWord_2284829, baseEnd_2284829] using wordTrace_append hprefix tailTrace_2284829
  have hstable : (prefixWord ++ tailWord_2284829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284829).length < 2 ^ (prefixWord ++ tailWord_2284829).sum := by decide
  have hdescent : baseEnd_2284829 < baseStart_2284829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284842 : List Nat := [3, 1, 4, 2, 1, 1, 3, 2, 6]
def baseStart_2284842 : Nat := 118140960795 + 2284842 * 2 ^ 59
def prefixEnd_2284842 : Nat := 4983230072969 + 3 ^ 40 * 2284842 * 2
def baseEnd_2284842 : Nat := 130358018397806086540801

theorem tailTrace_2284842 : CollatzResearch.WordTrace tailWord_2284842 prefixEnd_2284842 130358018397806086540801 := by
  unfold tailWord_2284842
  simp only [CollatzResearch.WordTrace]
  refine ⟨20833758497103782197928195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55556689325610085861141853 20833758497103782197928195)
  ·
    refine ⟨31250637745655673296892293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20833758497103782197928195 31250637745655673296892293)
    ·
      refine ⟨5859494577310438743167305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31250637745655673296892293 5859494577310438743167305)
      ·
        refine ⟨4394620932982829057375479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5859494577310438743167305 4394620932982829057375479)
        ·
          refine ⟨6591931399474243586063219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4394620932982829057375479 6591931399474243586063219)
          ·
            refine ⟨9887897099211365379094829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6591931399474243586063219 9887897099211365379094829)
            ·
              refine ⟨3707961412204262017160561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9887897099211365379094829 3707961412204262017160561)
              ·
                refine ⟨2780971059153196512870421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3707961412204262017160561 2780971059153196512870421)
                ·
                  refine ⟨130358018397806086540801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2780971059153196512870421 130358018397806086540801)
                  ·
                    rfl

theorem cell23_2284842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 6].length) (baseStart_2284842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284842 prefixEnd_2284842 := by exact prefixLift 2284842
  have htrace : WordTrace (prefixWord ++ tailWord_2284842) baseStart_2284842 baseEnd_2284842 := by
    simpa [prefixWord, tailWord_2284842, baseEnd_2284842] using wordTrace_append hprefix tailTrace_2284842
  have hstable : (prefixWord ++ tailWord_2284842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284842).length < 2 ^ (prefixWord ++ tailWord_2284842).sum := by decide
  have hdescent : baseEnd_2284842 < baseStart_2284842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284862 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 3, 5, 2]
def baseStart_2284862 : Nat := 118140960795 + 2284862 * 2 ^ 59
def prefixEnd_2284862 : Nat := 4983230072969 + 3 ^ 40 * 2284862 * 2
def baseEnd_2284862 : Nat := 1173232435193344700617117

theorem tailTrace_2284862 : CollatzResearch.WordTrace tailWord_2284862 prefixEnd_2284862 1173232435193344700617117 := by
  unfold tailWord_2284862
  simp only [CollatzResearch.WordTrace]
  refine ⟨10416970431042834025930105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55557175632228448138293893 10416970431042834025930105)
  ·
    refine ⟨7812727823282125519447579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10416970431042834025930105 7812727823282125519447579)
    ·
      refine ⟨11719091734923188279171369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7812727823282125519447579 11719091734923188279171369)
      ·
        refine ⟨8789318801192391209378527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11719091734923188279171369 8789318801192391209378527)
        ·
          refine ⟨13183978201788586814067791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8789318801192391209378527 13183978201788586814067791)
          ·
            refine ⟨19775967302682880221101687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13183978201788586814067791 19775967302682880221101687)
            ·
              refine ⟨29663950954024320331652531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19775967302682880221101687 29663950954024320331652531)
              ·
                refine ⟨44495926431036480497478797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29663950954024320331652531 44495926431036480497478797)
                ·
                  refine ⟨16685972411638680186554549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44495926431036480497478797 16685972411638680186554549)
                  ·
                    refine ⟨1564309913591126267489489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16685972411638680186554549 1564309913591126267489489)
                    ·
                      refine ⟨1173232435193344700617117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1564309913591126267489489 1173232435193344700617117)
                      ·
                        rfl

theorem cell23_2284862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_2284862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284862 prefixEnd_2284862 := by exact prefixLift 2284862
  have htrace : WordTrace (prefixWord ++ tailWord_2284862) baseStart_2284862 baseEnd_2284862 := by
    simpa [prefixWord, tailWord_2284862, baseEnd_2284862] using wordTrace_append hprefix tailTrace_2284862
  have hstable : (prefixWord ++ tailWord_2284862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284862).length < 2 ^ (prefixWord ++ tailWord_2284862).sum := by decide
  have hdescent : baseEnd_2284862 < baseStart_2284862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284895 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 3]
def baseStart_2284895 : Nat := 118140960795 + 2284895 * 2 ^ 59
def prefixEnd_2284895 : Nat := 4983230072969 + 3 ^ 40 * 2284895 * 2
def baseEnd_2284895 : Nat := 1173249380054943071504465

theorem tailTrace_2284895 : CollatzResearch.WordTrace tailWord_2284895 prefixEnd_2284895 1173249380054943071504465 := by
  unfold tailWord_2284895
  simp only [CollatzResearch.WordTrace]
  refine ⟨83336967057223118843392139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55557978038148745895594759 83336967057223118843392139)
  ·
    refine ⟨125005450585834678265088209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83336967057223118843392139 125005450585834678265088209)
    ·
      refine ⟨93754087939376008698816157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125005450585834678265088209 93754087939376008698816157)
      ·
        refine ⟨35157782977266003262056059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93754087939376008698816157 35157782977266003262056059)
        ·
          refine ⟨52736674465899004893084089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35157782977266003262056059 52736674465899004893084089)
          ·
            refine ⟨39552505849424253669813067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52736674465899004893084089 39552505849424253669813067)
            ·
              refine ⟨59328758774136380504719601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39552505849424253669813067 59328758774136380504719601)
              ·
                refine ⟨44496569080602285378539701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59328758774136380504719601 44496569080602285378539701)
                ·
                  refine ⟨4171553351306464254238097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44496569080602285378539701 4171553351306464254238097)
                  ·
                    refine ⟨3128665013479848190678573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4171553351306464254238097 3128665013479848190678573)
                    ·
                      refine ⟨1173249380054943071504465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3128665013479848190678573 1173249380054943071504465)
                      ·
                        rfl

theorem cell23_2284895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_2284895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284895 prefixEnd_2284895 := by exact prefixLift 2284895
  have htrace : WordTrace (prefixWord ++ tailWord_2284895) baseStart_2284895 baseEnd_2284895 := by
    simpa [prefixWord, tailWord_2284895, baseEnd_2284895] using wordTrace_append hprefix tailTrace_2284895
  have hstable : (prefixWord ++ tailWord_2284895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284895).length < 2 ^ (prefixWord ++ tailWord_2284895).sum := by decide
  have hdescent : baseEnd_2284895 < baseStart_2284895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284903 : List Nat := [1, 1, 5, 1, 4, 1, 3, 2, 1, 1, 3]
def baseStart_2284903 : Nat := 118140960795 + 2284903 * 2 ^ 59
def prefixEnd_2284903 : Nat := 4983230072969 + 3 ^ 40 * 2284903 * 2
def baseEnd_2284903 : Nat := 1173253487900179040204429

theorem tailTrace_2284903 : CollatzResearch.WordTrace tailWord_2284903 prefixEnd_2284903 1173253487900179040204429 := by
  unfold tailWord_2284903
  simp only [CollatzResearch.WordTrace]
  refine ⟨83337258841194136209683363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55558172560796090806455575 83337258841194136209683363)
  ·
    refine ⟨125005888261791204314525045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83337258841194136209683363 125005888261791204314525045)
    ·
      refine ⟨11719302024542925404486723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125005888261791204314525045 11719302024542925404486723)
      ·
        refine ⟨17578953036814388106730085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11719302024542925404486723 17578953036814388106730085)
        ·
          refine ⟨3296053694402697770011891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17578953036814388106730085 3296053694402697770011891)
          ·
            refine ⟨4944080541604046655017837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3296053694402697770011891 4944080541604046655017837)
            ·
              refine ⟨1854030203101517495631689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4944080541604046655017837 1854030203101517495631689)
              ·
                refine ⟨1390522652326138121723767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1854030203101517495631689 1390522652326138121723767)
                ·
                  refine ⟨2085783978489207182585651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1390522652326138121723767 2085783978489207182585651)
                  ·
                    refine ⟨3128675967733810773878477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2085783978489207182585651 3128675967733810773878477)
                    ·
                      refine ⟨1173253487900179040204429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3128675967733810773878477 1173253487900179040204429)
                      ·
                        rfl

theorem cell23_2284903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_2284903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284903 prefixEnd_2284903 := by exact prefixLift 2284903
  have htrace : WordTrace (prefixWord ++ tailWord_2284903) baseStart_2284903 baseEnd_2284903 := by
    simpa [prefixWord, tailWord_2284903, baseEnd_2284903] using wordTrace_append hprefix tailTrace_2284903
  have hstable : (prefixWord ++ tailWord_2284903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284903).length < 2 ^ (prefixWord ++ tailWord_2284903).sum := by decide
  have hdescent : baseEnd_2284903 < baseStart_2284903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284926 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2284926 : Nat := 118140960795 + 2284926 * 2 ^ 59
def prefixEnd_2284926 : Nat := 4983230072969 + 3 ^ 40 * 2284926 * 2
def baseEnd_2284926 : Nat := 1173265297955232450216823

theorem tailTrace_2284926 : CollatzResearch.WordTrace tailWord_2284926 prefixEnd_2284926 1173265297955232450216823 := by
  unfold tailWord_2284926
  simp only [CollatzResearch.WordTrace]
  refine ⟨10417262215013851392221329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55558731813407207425180421 10417262215013851392221329)
  ·
    refine ⟨7812946661260388544165997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10417262215013851392221329 7812946661260388544165997)
    ·
      refine ⟨2929854997972645704062249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7812946661260388544165997 2929854997972645704062249)
      ·
        refine ⟨2197391248479484278046687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2929854997972645704062249 2197391248479484278046687)
        ·
          refine ⟨3296086872719226417070031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2197391248479484278046687 3296086872719226417070031)
          ·
            refine ⟨4944130309078839625605047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3296086872719226417070031 4944130309078839625605047)
            ·
              refine ⟨7416195463618259438407571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4944130309078839625605047 7416195463618259438407571)
              ·
                refine ⟨11124293195427389157611357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7416195463618259438407571 11124293195427389157611357)
                ·
                  refine ⟨4171609948285270934104259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11124293195427389157611357 4171609948285270934104259)
                  ·
                    refine ⟨6257414922427906401156389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4171609948285270934104259 6257414922427906401156389)
                    ·
                      refine ⟨1173265297955232450216823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6257414922427906401156389 1173265297955232450216823)
                      ·
                        rfl

theorem cell23_2284926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2284926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284926 prefixEnd_2284926 := by exact prefixLift 2284926
  have htrace : WordTrace (prefixWord ++ tailWord_2284926) baseStart_2284926 baseEnd_2284926 := by
    simpa [prefixWord, tailWord_2284926, baseEnd_2284926] using wordTrace_append hprefix tailTrace_2284926
  have hstable : (prefixWord ++ tailWord_2284926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284926).length < 2 ^ (prefixWord ++ tailWord_2284926).sum := by decide
  have hdescent : baseEnd_2284926 < baseStart_2284926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284929 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_2284929 : Nat := 118140960795 + 2284929 * 2 ^ 59
def prefixEnd_2284929 : Nat := 4983230072969 + 3 ^ 40 * 2284929 * 2
def baseEnd_2284929 : Nat := 1173266838397195938479309

theorem tailTrace_2284929 : CollatzResearch.WordTrace tailWord_2284929 prefixEnd_2284929 1173266838397195938479309 := by
  unfold tailWord_2284929
  simp only [CollatzResearch.WordTrace]
  refine ⟨83338207139099942650129841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55558804759399961766753227 83338207139099942650129841)
  ·
    refine ⟨62503655354324956987597381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83338207139099942650129841 62503655354324956987597381)
    ·
      refine ⟨11719435378935929435174509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62503655354324956987597381 11719435378935929435174509)
      ·
        refine ⟨4394788267100973538190441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11719435378935929435174509 4394788267100973538190441)
        ·
          refine ⟨3296091200325730153642831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4394788267100973538190441 3296091200325730153642831)
          ·
            refine ⟨4944136800488595230464247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3296091200325730153642831 4944136800488595230464247)
            ·
              refine ⟨7416205200732892845696371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4944136800488595230464247 7416205200732892845696371)
              ·
                refine ⟨11124307801099339268544557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7416205200732892845696371 11124307801099339268544557)
                ·
                  refine ⟨4171615425412252225704209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11124307801099339268544557 4171615425412252225704209)
                  ·
                    refine ⟨3128711569059189169278157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4171615425412252225704209 3128711569059189169278157)
                    ·
                      refine ⟨1173266838397195938479309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3128711569059189169278157 1173266838397195938479309)
                      ·
                        rfl

theorem cell23_2284929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_2284929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284929 prefixEnd_2284929 := by exact prefixLift 2284929
  have htrace : WordTrace (prefixWord ++ tailWord_2284929) baseStart_2284929 baseEnd_2284929 := by
    simpa [prefixWord, tailWord_2284929, baseEnd_2284929] using wordTrace_append hprefix tailTrace_2284929
  have hstable : (prefixWord ++ tailWord_2284929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284929).length < 2 ^ (prefixWord ++ tailWord_2284929).sum := by decide
  have hdescent : baseEnd_2284929 < baseStart_2284929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284946 : List Nat := [3, 2, 3, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2284946 : Nat := 118140960795 + 2284946 * 2 ^ 59
def prefixEnd_2284946 : Nat := 4983230072969 + 3 ^ 40 * 2284946 * 2
def baseEnd_2284946 : Nat := 1173275567568322371966731

theorem tailTrace_2284946 : CollatzResearch.WordTrace tailWord_2284946 prefixEnd_2284946 1173275567568322371966731 := by
  unfold tailWord_2284946
  simp only [CollatzResearch.WordTrace]
  refine ⟨20834706795009588638374673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55559218120025569702332461 20834706795009588638374673)
  ·
    refine ⟨15626030096257191478781005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20834706795009588638374673 15626030096257191478781005)
    ·
      refine ⟨5859761286096446804542877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15626030096257191478781005 5859761286096446804542877)
      ·
        refine ⟨2197410482286167551703579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5859761286096446804542877 2197410482286167551703579)
        ·
          refine ⟨3296115723429251327555369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2197410482286167551703579 3296115723429251327555369)
          ·
            refine ⟨2472086792571938495666527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3296115723429251327555369 2472086792571938495666527)
            ·
              refine ⟨3708130188857907743499791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2472086792571938495666527 3708130188857907743499791)
              ·
                refine ⟨5562195283286861615249687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3708130188857907743499791 5562195283286861615249687)
                ·
                  refine ⟨8343292924930292422874531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5562195283286861615249687 8343292924930292422874531)
                  ·
                    refine ⟨12514939387395438634311797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8343292924930292422874531 12514939387395438634311797)
                    ·
                      refine ⟨1173275567568322371966731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12514939387395438634311797 1173275567568322371966731)
                      ·
                        rfl

theorem cell23_2284946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2284946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284946 prefixEnd_2284946 := by exact prefixLift 2284946
  have htrace : WordTrace (prefixWord ++ tailWord_2284946) baseStart_2284946 baseEnd_2284946 := by
    simpa [prefixWord, tailWord_2284946, baseEnd_2284946] using wordTrace_append hprefix tailTrace_2284946
  have hstable : (prefixWord ++ tailWord_2284946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284946).length < 2 ^ (prefixWord ++ tailWord_2284946).sum := by decide
  have hdescent : baseEnd_2284946 < baseStart_2284946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284959 : List Nat := [1, 1, 2, 5, 1, 2, 1, 4, 2, 1, 3]
def baseStart_2284959 : Nat := 118140960795 + 2284959 * 2 ^ 59
def prefixEnd_2284959 : Nat := 4983230072969 + 3 ^ 40 * 2284959 * 2
def baseEnd_2284959 : Nat := 1173282242816830821104171

theorem tailTrace_2284959 : CollatzResearch.WordTrace tailWord_2284959 prefixEnd_2284959 1173282242816830821104171 := by
  unfold tailWord_2284959
  simp only [CollatzResearch.WordTrace]
  refine ⟨83339301328991257773721931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55559534219327505182481287 83339301328991257773721931)
  ·
    refine ⟨125008951993486886660582897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83339301328991257773721931 125008951993486886660582897)
    ·
      refine ⟨93756713995115164995437173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125008951993486886660582897 93756713995115164995437173)
      ·
        refine ⟨8789691937042046718322235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93756713995115164995437173 8789691937042046718322235)
        ·
          refine ⟨13184537905563070077483353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8789691937042046718322235 13184537905563070077483353)
          ·
            refine ⟨9888403429172302558112515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13184537905563070077483353 9888403429172302558112515)
            ·
              refine ⟨14832605143758453837168773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9888403429172302558112515 14832605143758453837168773)
              ·
                refine ⟨2781113464454710094469145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14832605143758453837168773 2781113464454710094469145)
                ·
                  refine ⟨2085835098341032570851859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2781113464454710094469145 2085835098341032570851859)
                  ·
                    refine ⟨3128752647511548856277789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2085835098341032570851859 3128752647511548856277789)
                    ·
                      refine ⟨1173282242816830821104171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3128752647511548856277789 1173282242816830821104171)
                      ·
                        rfl

theorem cell23_2284959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_2284959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284959 prefixEnd_2284959 := by exact prefixLift 2284959
  have htrace : WordTrace (prefixWord ++ tailWord_2284959) baseStart_2284959 baseEnd_2284959 := by
    simpa [prefixWord, tailWord_2284959, baseEnd_2284959] using wordTrace_append hprefix tailTrace_2284959
  have hstable : (prefixWord ++ tailWord_2284959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284959).length < 2 ^ (prefixWord ++ tailWord_2284959).sum := by decide
  have hdescent : baseEnd_2284959 < baseStart_2284959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284994 : List Nat := [3, 5, 2, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_2284994 : Nat := 118140960795 + 2284994 * 2 ^ 59
def prefixEnd_2284994 : Nat := 4983230072969 + 3 ^ 40 * 2284994 * 2
def baseEnd_2284994 : Nat := 1173300214639738184166511

theorem tailTrace_2284994 : CollatzResearch.WordTrace tailWord_2284994 prefixEnd_2284994 1173300214639738184166511 := by
  unfold tailWord_2284994
  simp only [CollatzResearch.WordTrace]
  refine ⟨20835144470966114687811509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55560385255909639167497357 20835144470966114687811509)
  ·
    refine ⟨1953294794153073251982329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20835144470966114687811509 1953294794153073251982329)
    ·
      refine ⟨1464971095614804938986747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1953294794153073251982329 1464971095614804938986747)
      ·
        refine ⟨2197456643422207408480121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1464971095614804938986747 2197456643422207408480121)
        ·
          refine ⟨1648092482566655556360091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2197456643422207408480121 1648092482566655556360091)
          ·
            refine ⟨2472138723849983334540137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1648092482566655556360091 2472138723849983334540137)
            ·
              refine ⟨1854104042887487500905103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2472138723849983334540137 1854104042887487500905103)
              ·
                refine ⟨2781156064331231251357655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854104042887487500905103 2781156064331231251357655)
                ·
                  refine ⟨4171734096496846877036483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2781156064331231251357655 4171734096496846877036483)
                  ·
                    refine ⟨6257601144745270315554725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4171734096496846877036483 6257601144745270315554725)
                    ·
                      refine ⟨1173300214639738184166511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6257601144745270315554725 1173300214639738184166511)
                      ·
                        rfl

theorem cell23_2284994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_2284994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284994 prefixEnd_2284994 := by exact prefixLift 2284994
  have htrace : WordTrace (prefixWord ++ tailWord_2284994) baseStart_2284994 baseEnd_2284994 := by
    simpa [prefixWord, tailWord_2284994, baseEnd_2284994] using wordTrace_append hprefix tailTrace_2284994
  have hstable : (prefixWord ++ tailWord_2284994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284994).length < 2 ^ (prefixWord ++ tailWord_2284994).sum := by decide
  have hdescent : baseEnd_2284994 < baseStart_2284994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284999 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 4, 2, 2]
def baseStart_2284999 : Nat := 118140960795 + 2284999 * 2 ^ 59
def prefixEnd_2284999 : Nat := 4983230072969 + 3 ^ 40 * 2284999 * 2
def baseEnd_2284999 : Nat := 1173302782043010664603987

theorem tailTrace_2284999 : CollatzResearch.WordTrace tailWord_2284999 prefixEnd_2284999 1173302782043010664603987 := by
  unfold tailWord_2284999
  simp only [CollatzResearch.WordTrace]
  refine ⟨83340760248846344605178051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55560506832564229736785367 83340760248846344605178051)
  ·
    refine ⟨125011140373269516907767077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83340760248846344605178051 125011140373269516907767077)
    ·
      refine ⟨23439588819988034420206327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125011140373269516907767077 23439588819988034420206327)
      ·
        refine ⟨35159383229982051630309491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23439588819988034420206327 35159383229982051630309491)
        ·
          refine ⟨52739074844973077445464237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35159383229982051630309491 52739074844973077445464237)
          ·
            refine ⟨19777153066864904042049089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52739074844973077445464237 19777153066864904042049089)
            ·
              refine ⟨14832864800148678031536817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19777153066864904042049089 14832864800148678031536817)
              ·
                refine ⟨11124648600111508523652613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14832864800148678031536817 11124648600111508523652613)
                ·
                  refine ⟨2085871612520907848184865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11124648600111508523652613 2085871612520907848184865)
                  ·
                    refine ⟨1564403709390680886138649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2085871612520907848184865 1564403709390680886138649)
                    ·
                      refine ⟨1173302782043010664603987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1564403709390680886138649 1173302782043010664603987)
                      ·
                        rfl

theorem cell23_2284999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_2284999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2284999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2284999 prefixEnd_2284999 := by exact prefixLift 2284999
  have htrace : WordTrace (prefixWord ++ tailWord_2284999) baseStart_2284999 baseEnd_2284999 := by
    simpa [prefixWord, tailWord_2284999, baseEnd_2284999] using wordTrace_append hprefix tailTrace_2284999
  have hstable : (prefixWord ++ tailWord_2284999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284999).length < 2 ^ (prefixWord ++ tailWord_2284999).sum := by decide
  have hdescent : baseEnd_2284999 < baseStart_2284999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285016 : List Nat := [2, 1, 2, 2, 2, 1, 5, 2, 2, 2, 2]
def baseStart_2285016 : Nat := 118140960795 + 2285016 * 2 ^ 59
def prefixEnd_2285016 : Nat := 4983230072969 + 3 ^ 40 * 2285016 * 2
def baseEnd_2285016 : Nat := 1173311511214137098091409

theorem tailTrace_2285016 : CollatzResearch.WordTrace tailWord_2285016 prefixEnd_2285016 1173311511214137098091409 := by
  unfold tailWord_2285016
  simp only [CollatzResearch.WordTrace]
  refine ⟨41670690144892378254273451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55560920193189837672364601 41670690144892378254273451)
  ·
    refine ⟨62506035217338567381410177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41670690144892378254273451 62506035217338567381410177)
    ·
      refine ⟨46879526413003925536057633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62506035217338567381410177 46879526413003925536057633)
      ·
        refine ⟨35159644809752944152043225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46879526413003925536057633 35159644809752944152043225)
        ·
          refine ⟨26369733607314708114032419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35159644809752944152043225 26369733607314708114032419)
          ·
            refine ⟨39554600410972062171048629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26369733607314708114032419 39554600410972062171048629)
            ·
              refine ⟨3708243788528630828535809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39554600410972062171048629 3708243788528630828535809)
              ·
                refine ⟨2781182841396473121401857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3708243788528630828535809 2781182841396473121401857)
                ·
                  refine ⟨2085887131047354841051393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2781182841396473121401857 2085887131047354841051393)
                  ·
                    refine ⟨1564415348285516130788545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2085887131047354841051393 1564415348285516130788545)
                    ·
                      refine ⟨1173311511214137098091409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1564415348285516130788545 1173311511214137098091409)
                      ·
                        rfl

theorem cell23_2285016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_2285016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285016 prefixEnd_2285016 := by exact prefixLift 2285016
  have htrace : WordTrace (prefixWord ++ tailWord_2285016) baseStart_2285016 baseEnd_2285016 := by
    simpa [prefixWord, tailWord_2285016, baseEnd_2285016] using wordTrace_append hprefix tailTrace_2285016
  have hstable : (prefixWord ++ tailWord_2285016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285016).length < 2 ^ (prefixWord ++ tailWord_2285016).sum := by decide
  have hdescent : baseEnd_2285016 < baseStart_2285016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285032 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_2285032 : Nat := 118140960795 + 2285032 * 2 ^ 59
def prefixEnd_2285032 : Nat := 4983230072969 + 3 ^ 40 * 2285032 * 2
def baseEnd_2285032 : Nat := 1173319726904609035491335

theorem tailTrace_2285032 : CollatzResearch.WordTrace tailWord_2285032 prefixEnd_2285032 1173319726904609035491335 := by
  unfold tailWord_2285032
  simp only [CollatzResearch.WordTrace]
  refine ⟨41670981928863395620564675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55561309238484527494086233 41670981928863395620564675)
  ·
    refine ⟨62506472893295093430847013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41670981928863395620564675 62506472893295093430847013)
    ·
      refine ⟨11719963667492830018283815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62506472893295093430847013 11719963667492830018283815)
      ·
        refine ⟨17579945501239245027425723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11719963667492830018283815 17579945501239245027425723)
        ·
          refine ⟨26369918251858867541138585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17579945501239245027425723 26369918251858867541138585)
          ·
            refine ⟨19777438688894150655853939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26369918251858867541138585 19777438688894150655853939)
            ·
              refine ⟨29666158033341225983780909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19777438688894150655853939 29666158033341225983780909)
              ·
                refine ⟨11124809262502959743917841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29666158033341225983780909 11124809262502959743917841)
                ·
                  refine ⟨8343606946877219807938381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11124809262502959743917841 8343606946877219807938381)
                  ·
                    refine ⟨3128852605078957427976893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8343606946877219807938381 3128852605078957427976893)
                    ·
                      refine ⟨1173319726904609035491335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3128852605078957427976893 1173319726904609035491335)
                      ·
                        rfl

theorem cell23_2285032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_2285032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285032 prefixEnd_2285032 := by exact prefixLift 2285032
  have htrace : WordTrace (prefixWord ++ tailWord_2285032) baseStart_2285032 baseEnd_2285032 := by
    simpa [prefixWord, tailWord_2285032, baseEnd_2285032] using wordTrace_append hprefix tailTrace_2285032
  have hstable : (prefixWord ++ tailWord_2285032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285032).length < 2 ^ (prefixWord ++ tailWord_2285032).sum := by decide
  have hdescent : baseEnd_2285032 < baseStart_2285032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285035 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 6, 5]
def baseStart_2285035 : Nat := 118140960795 + 2285035 * 2 ^ 59
def prefixEnd_2285035 : Nat := 4983230072969 + 3 ^ 40 * 2285035 * 2
def baseEnd_2285035 : Nat := 391107089115524174584607

theorem tailTrace_2285035 : CollatzResearch.WordTrace tailWord_2285035 prefixEnd_2285035 391107089115524174584607 := by
  unfold tailWord_2285035
  simp only [CollatzResearch.WordTrace]
  refine ⟨83342073276715922753488559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55561382184477281835659039 83342073276715922753488559)
  ·
    refine ⟨125013109915073884130232839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83342073276715922753488559 125013109915073884130232839)
    ·
      refine ⟨187519664872610826195349259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125013109915073884130232839 187519664872610826195349259)
      ·
        refine ⟨281279497308916239293023889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187519664872610826195349259 281279497308916239293023889)
        ·
          refine ⟨210959622981687179469767917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281279497308916239293023889 210959622981687179469767917)
          ·
            refine ⟨79109858618132692301162969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210959622981687179469767917 79109858618132692301162969)
            ·
              refine ⟨59332393963599519225872227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79109858618132692301162969 59332393963599519225872227)
              ·
                refine ⟨88998590945399278838808341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59332393963599519225872227 88998590945399278838808341)
                ·
                  refine ⟨4171808950565591195569141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88998590945399278838808341 4171808950565591195569141)
                  ·
                    refine ⟨391107089115524174584607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4171808950565591195569141 391107089115524174584607)
                    ·
                      rfl

theorem cell23_2285035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 5].length) (baseStart_2285035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285035 prefixEnd_2285035 := by exact prefixLift 2285035
  have htrace : WordTrace (prefixWord ++ tailWord_2285035) baseStart_2285035 baseEnd_2285035 := by
    simpa [prefixWord, tailWord_2285035, baseEnd_2285035] using wordTrace_append hprefix tailTrace_2285035
  have hstable : (prefixWord ++ tailWord_2285035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285035).length < 2 ^ (prefixWord ++ tailWord_2285035).sum := by decide
  have hdescent : baseEnd_2285035 < baseStart_2285035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285109 : List Nat := [1, 3, 3, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_2285109 : Nat := 118140960795 + 2285109 * 2 ^ 59
def prefixEnd_2285109 : Nat := 4983230072969 + 3 ^ 40 * 2285109 * 2
def baseEnd_2285109 : Nat := 1173359264915005234228481

theorem tailTrace_2285109 : CollatzResearch.WordTrace tailWord_2285109 prefixEnd_2285109 1173359264915005234228481 := by
  unfold tailWord_2285109
  simp only [CollatzResearch.WordTrace]
  refine ⟨83344772278447833391682381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55563181518965222261121587 83344772278447833391682381)
  ·
    refine ⟨31254289604417937521880893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83344772278447833391682381 31254289604417937521880893)
    ·
      refine ⟨11720358601656726570705335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31254289604417937521880893 11720358601656726570705335)
      ·
        refine ⟨17580537902485089856058003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11720358601656726570705335 17580537902485089856058003)
        ·
          refine ⟨26370806853727634784087005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17580537902485089856058003 26370806853727634784087005)
          ·
            refine ⟨9889052570147863044032627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26370806853727634784087005 9889052570147863044032627)
            ·
              refine ⟨14833578855221794566048941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9889052570147863044032627 14833578855221794566048941)
              ·
                refine ⟨5562592070708172962268353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14833578855221794566048941 5562592070708172962268353)
                ·
                  refine ⟨4171944053031129721701265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5562592070708172962268353 4171944053031129721701265)
                  ·
                    refine ⟨3128958039773347291275949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4171944053031129721701265 3128958039773347291275949)
                    ·
                      refine ⟨1173359264915005234228481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3128958039773347291275949 1173359264915005234228481)
                      ·
                        rfl

theorem cell23_2285109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_2285109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285109 prefixEnd_2285109 := by exact prefixLift 2285109
  have htrace : WordTrace (prefixWord ++ tailWord_2285109) baseStart_2285109 baseEnd_2285109 := by
    simpa [prefixWord, tailWord_2285109, baseEnd_2285109] using wordTrace_append hprefix tailTrace_2285109
  have hstable : (prefixWord ++ tailWord_2285109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285109).length < 2 ^ (prefixWord ++ tailWord_2285109).sum := by decide
  have hdescent : baseEnd_2285109 < baseStart_2285109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285156 : List Nat := [2, 3, 1, 1, 2, 4, 1, 2, 3, 1, 3]
def baseStart_2285156 : Nat := 118140960795 + 2285156 * 2 ^ 59
def prefixEnd_2285156 : Nat := 4983230072969 + 3 ^ 40 * 2285156 * 2
def baseEnd_2285156 : Nat := 1173383398505766550340765

theorem tailTrace_2285156 : CollatzResearch.WordTrace tailWord_2285156 prefixEnd_2285156 1173383398505766550340765 := by
  unfold tailWord_2285156
  simp only [CollatzResearch.WordTrace]
  refine ⟨41673243254638780209321661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55564324339518373612428881 41673243254638780209321661)
  ·
    refine ⟨15627466220489542578495623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41673243254638780209321661 15627466220489542578495623)
    ·
      refine ⟨23441199330734313867743435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15627466220489542578495623 23441199330734313867743435)
      ·
        refine ⟨35161798996101470801615153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23441199330734313867743435 35161798996101470801615153)
        ·
          refine ⟨26371349247076103101211365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35161798996101470801615153 26371349247076103101211365)
          ·
            refine ⟨4944627983826769331477131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26371349247076103101211365 4944627983826769331477131)
            ·
              refine ⟨7416941975740153997215697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4944627983826769331477131 7416941975740153997215697)
              ·
                refine ⟨5562706481805115497911773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7416941975740153997215697 5562706481805115497911773)
                ·
                  refine ⟨2086014930676918311716915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5562706481805115497911773 2086014930676918311716915)
                  ·
                    refine ⟨3129022396015377467575373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2086014930676918311716915 3129022396015377467575373)
                    ·
                      refine ⟨1173383398505766550340765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3129022396015377467575373 1173383398505766550340765)
                      ·
                        rfl

theorem cell23_2285156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_2285156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285156 prefixEnd_2285156 := by exact prefixLift 2285156
  have htrace : WordTrace (prefixWord ++ tailWord_2285156) baseStart_2285156 baseEnd_2285156 := by
    simpa [prefixWord, tailWord_2285156, baseEnd_2285156] using wordTrace_append hprefix tailTrace_2285156
  have hstable : (prefixWord ++ tailWord_2285156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285156).length < 2 ^ (prefixWord ++ tailWord_2285156).sum := by decide
  have hdescent : baseEnd_2285156 < baseStart_2285156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285179 : List Nat := [1, 1, 1, 1, 1, 4, 5, 3, 1, 1, 4]
def baseStart_2285179 : Nat := 118140960795 + 2285179 * 2 ^ 59
def prefixEnd_2285179 : Nat := 4983230072969 + 3 ^ 40 * 2285179 * 2
def baseEnd_2285179 : Nat := 1173395208560819960353159

theorem tailTrace_2285179 : CollatzResearch.WordTrace tailWord_2285179 prefixEnd_2285179 1173395208560819960353159 := by
  unfold tailWord_2285179
  simp only [CollatzResearch.WordTrace]
  refine ⟨83347325388194235346730591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55564883592129490231153727 83347325388194235346730591)
  ·
    refine ⟨125020988082291353020095887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83347325388194235346730591 125020988082291353020095887)
    ·
      refine ⟨187531482123437029530143831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125020988082291353020095887 187531482123437029530143831)
      ·
        refine ⟨281297223185155544295215747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187531482123437029530143831 281297223185155544295215747)
        ·
          refine ⟨421945834777733316442823621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281297223185155544295215747 421945834777733316442823621)
          ·
            refine ⟨79114844020824996833029429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 421945834777733316442823621 79114844020824996833029429)
            ·
              refine ⟨7417016626952343453096509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79114844020824996833029429 7417016626952343453096509)
              ·
                refine ⟨2781381235107128794911191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7417016626952343453096509 2781381235107128794911191)
                ·
                  refine ⟨4172071852660693192366787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2781381235107128794911191 4172071852660693192366787)
                  ·
                    refine ⟨6258107778991039788550181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4172071852660693192366787 6258107778991039788550181)
                    ·
                      refine ⟨1173395208560819960353159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6258107778991039788550181 1173395208560819960353159)
                      ·
                        rfl

theorem cell23_2285179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 1, 4].length) (baseStart_2285179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285179 prefixEnd_2285179 := by exact prefixLift 2285179
  have htrace : WordTrace (prefixWord ++ tailWord_2285179) baseStart_2285179 baseEnd_2285179 := by
    simpa [prefixWord, tailWord_2285179, baseEnd_2285179] using wordTrace_append hprefix tailTrace_2285179
  have hstable : (prefixWord ++ tailWord_2285179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285179).length < 2 ^ (prefixWord ++ tailWord_2285179).sum := by decide
  have hdescent : baseEnd_2285179 < baseStart_2285179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285189 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 4, 4]
def baseStart_2285189 : Nat := 118140960795 + 2285189 * 2 ^ 59
def prefixEnd_2285189 : Nat := 4983230072969 + 3 ^ 40 * 2285189 * 2
def baseEnd_2285189 : Nat := 391133447789121640409371

theorem tailTrace_2285189 : CollatzResearch.WordTrace tailWord_2285189 prefixEnd_2285189 391133447789121640409371 := by
  unfold tailWord_2285189
  simp only [CollatzResearch.WordTrace]
  refine ⟨83347690118158007054594621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55565126745438671369729747 83347690118158007054594621)
  ·
    refine ⟨31255383794309252645472983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83347690118158007054594621 31255383794309252645472983)
    ·
      refine ⟨46883075691463878968209475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31255383794309252645472983 46883075691463878968209475)
      ·
        refine ⟨70324613537195818452314213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46883075691463878968209475 70324613537195818452314213)
        ·
          refine ⟨13185865038224215959808915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70324613537195818452314213 13185865038224215959808915)
          ·
            refine ⟨19778797557336323939713373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13185865038224215959808915 19778797557336323939713373)
            ·
              refine ⟨7417049084001121477392515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19778797557336323939713373 7417049084001121477392515)
              ·
                refine ⟨11125573626001682216088773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7417049084001121477392515 11125573626001682216088773)
                ·
                  refine ⟨2086045054875315415516645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11125573626001682216088773 2086045054875315415516645)
                  ·
                    refine ⟨391133447789121640409371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2086045054875315415516645 391133447789121640409371)
                    ·
                      rfl

theorem cell23_2285189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_2285189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285189 prefixEnd_2285189 := by exact prefixLift 2285189
  have htrace : WordTrace (prefixWord ++ tailWord_2285189) baseStart_2285189 baseEnd_2285189 := by
    simpa [prefixWord, tailWord_2285189, baseEnd_2285189] using wordTrace_append hprefix tailTrace_2285189
  have hstable : (prefixWord ++ tailWord_2285189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285189).length < 2 ^ (prefixWord ++ tailWord_2285189).sum := by decide
  have hdescent : baseEnd_2285189 < baseStart_2285189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285216 : List Nat := [2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 3]
def baseStart_2285216 : Nat := 118140960795 + 2285216 * 2 ^ 59
def prefixEnd_2285216 : Nat := 4983230072969 + 3 ^ 40 * 2285216 * 2
def baseEnd_2285216 : Nat := 1173414207345036315590489

theorem tailTrace_2285216 : CollatzResearch.WordTrace tailWord_2285216 prefixEnd_2285216 1173414207345036315590489 := by
  unfold tailWord_2285216
  simp only [CollatzResearch.WordTrace]
  refine ⟨41674337444530095332913751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55565783259373460443885001 41674337444530095332913751)
  ·
    refine ⟨62511506166795142999370627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41674337444530095332913751 62511506166795142999370627)
    ·
      refine ⟨93767259250192714499055941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62511506166795142999370627 93767259250192714499055941)
      ·
        refine ⟨17581361109411133968572989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93767259250192714499055941 17581361109411133968572989)
        ·
          refine ⟨6593010416029175238214871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17581361109411133968572989 6593010416029175238214871)
          ·
            refine ⟨9889515624043762857322307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6593010416029175238214871 9889515624043762857322307)
            ·
              refine ⟨14834273436065644285983461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9889515624043762857322307 14834273436065644285983461)
              ·
                refine ⟨2781426269262308303621899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14834273436065644285983461 2781426269262308303621899)
                ·
                  refine ⟨4172139403893462455432849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2781426269262308303621899 4172139403893462455432849)
                  ·
                    refine ⟨3129104552920096841574637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4172139403893462455432849 3129104552920096841574637)
                    ·
                      refine ⟨1173414207345036315590489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3129104552920096841574637 1173414207345036315590489)
                      ·
                        rfl

theorem cell23_2285216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_2285216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285216 prefixEnd_2285216 := by exact prefixLift 2285216
  have htrace : WordTrace (prefixWord ++ tailWord_2285216) baseStart_2285216 baseEnd_2285216 := by
    simpa [prefixWord, tailWord_2285216, baseEnd_2285216] using wordTrace_append hprefix tailTrace_2285216
  have hstable : (prefixWord ++ tailWord_2285216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285216).length < 2 ^ (prefixWord ++ tailWord_2285216).sum := by decide
  have hdescent : baseEnd_2285216 < baseStart_2285216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285256 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 3, 3, 2]
def baseStart_2285256 : Nat := 118140960795 + 2285256 * 2 ^ 59
def prefixEnd_2285256 : Nat := 4983230072969 + 3 ^ 40 * 2285256 * 2
def baseEnd_2285256 : Nat := 1173434746571216159090305

theorem tailTrace_2285256 : CollatzResearch.WordTrace tailWord_2285256 prefixEnd_2285256 1173434746571216159090305 := by
  unfold tailWord_2285256
  simp only [CollatzResearch.WordTrace]
  refine ⟨41675066904457638748641811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55566755872610184998189081 41675066904457638748641811)
  ·
    refine ⟨62512600356686458122962717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41675066904457638748641811 62512600356686458122962717)
    ·
      refine ⟨23442225133757421796111019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62512600356686458122962717 23442225133757421796111019)
      ·
        refine ⟨35163337700636132694166529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23442225133757421796111019 35163337700636132694166529)
        ·
          refine ⟨26372503275477099520624897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35163337700636132694166529 26372503275477099520624897)
          ·
            refine ⟨19779377456607824640468673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26372503275477099520624897 19779377456607824640468673)
            ·
              refine ⟨14834533092455868480351505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19779377456607824640468673 14834533092455868480351505)
              ·
                refine ⟨11125899819341901360263629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14834533092455868480351505 11125899819341901360263629)
                ·
                  refine ⟨4172212432253213010098861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11125899819341901360263629 4172212432253213010098861)
                  ·
                    refine ⟨1564579662094954878787073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4172212432253213010098861 1564579662094954878787073)
                    ·
                      refine ⟨1173434746571216159090305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1564579662094954878787073 1173434746571216159090305)
                      ·
                        rfl

theorem cell23_2285256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_2285256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285256 prefixEnd_2285256 := by exact prefixLift 2285256
  have htrace : WordTrace (prefixWord ++ tailWord_2285256) baseStart_2285256 baseEnd_2285256 := by
    simpa [prefixWord, tailWord_2285256, baseEnd_2285256] using wordTrace_append hprefix tailTrace_2285256
  have hstable : (prefixWord ++ tailWord_2285256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285256).length < 2 ^ (prefixWord ++ tailWord_2285256).sum := by decide
  have hdescent : baseEnd_2285256 < baseStart_2285256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285273 : List Nat := [1, 2, 1, 2, 3, 3, 3, 2, 1, 3, 2]
def baseStart_2285273 : Nat := 118140960795 + 2285273 * 2 ^ 59
def prefixEnd_2285273 : Nat := 4983230072969 + 3 ^ 40 * 2285273 * 2
def baseEnd_2285273 : Nat := 1173443475742342592577727

theorem tailTrace_2285273 : CollatzResearch.WordTrace tailWord_2285273 prefixEnd_2285273 1173443475742342592577727 := by
  unfold tailWord_2285273
  simp only [CollatzResearch.WordTrace]
  refine ⟨83350753849853689400652473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55567169233235792933768315 83350753849853689400652473)
  ·
    refine ⟨62513065387390267050489355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83350753849853689400652473 62513065387390267050489355)
    ·
      refine ⟨93769598081085400575734033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62513065387390267050489355 93769598081085400575734033)
      ·
        refine ⟨70327198560814050431800525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93769598081085400575734033 70327198560814050431800525)
        ·
          refine ⟨26372699460305268911925197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70327198560814050431800525 26372699460305268911925197)
          ·
            refine ⟨9889762297614475841971949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26372699460305268911925197 9889762297614475841971949)
            ·
              refine ⟨3708660861605428440739481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9889762297614475841971949 3708660861605428440739481)
              ·
                refine ⟨2781495646204071330554611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3708660861605428440739481 2781495646204071330554611)
                ·
                  refine ⟨4172243469306106995831917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2781495646204071330554611 4172243469306106995831917)
                  ·
                    refine ⟨1564591300989790123436969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4172243469306106995831917 1564591300989790123436969)
                    ·
                      refine ⟨1173443475742342592577727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1564591300989790123436969 1173443475742342592577727)
                      ·
                        rfl

theorem cell23_2285273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 3, 2].length) (baseStart_2285273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285273 prefixEnd_2285273 := by exact prefixLift 2285273
  have htrace : WordTrace (prefixWord ++ tailWord_2285273) baseStart_2285273 baseEnd_2285273 := by
    simpa [prefixWord, tailWord_2285273, baseEnd_2285273] using wordTrace_append hprefix tailTrace_2285273
  have hstable : (prefixWord ++ tailWord_2285273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285273).length < 2 ^ (prefixWord ++ tailWord_2285273).sum := by decide
  have hdescent : baseEnd_2285273 < baseStart_2285273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285303 : List Nat := [1, 1, 3, 1, 1, 1, 5, 4, 2, 2, 2]
def baseStart_2285303 : Nat := 118140960795 + 2285303 * 2 ^ 59
def prefixEnd_2285303 : Nat := 4983230072969 + 3 ^ 40 * 2285303 * 2
def baseEnd_2285303 : Nat := 1173458880161977475202589

theorem tailTrace_2285303 : CollatzResearch.WordTrace tailWord_2285303 prefixEnd_2285303 1173458880161977475202589 := by
  unfold tailWord_2285303
  simp only [CollatzResearch.WordTrace]
  refine ⟨83351848039745004524244563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55567898693163336349496375 83351848039745004524244563)
  ·
    refine ⟨125027772059617506786366845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83351848039745004524244563 125027772059617506786366845)
    ·
      refine ⟨46885414522356565044887567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125027772059617506786366845 46885414522356565044887567)
      ·
        refine ⟨70328121783534847567331351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46885414522356565044887567 70328121783534847567331351)
        ·
          refine ⟨105492182675302271350997027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70328121783534847567331351 105492182675302271350997027)
          ·
            refine ⟨158238274012953407026495541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105492182675302271350997027 158238274012953407026495541)
            ·
              refine ⟨14834838188714381908733957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 158238274012953407026495541 14834838188714381908733957)
              ·
                refine ⟨2781532160383946607887617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14834838188714381908733957 2781532160383946607887617)
                ·
                  refine ⟨2086149120287959955915713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2781532160383946607887617 2086149120287959955915713)
                  ·
                    refine ⟨1564611840215969966936785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2086149120287959955915713 1564611840215969966936785)
                    ·
                      refine ⟨1173458880161977475202589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1564611840215969966936785 1173458880161977475202589)
                      ·
                        rfl

theorem cell23_2285303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 2, 2].length) (baseStart_2285303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285303 prefixEnd_2285303 := by exact prefixLift 2285303
  have htrace : WordTrace (prefixWord ++ tailWord_2285303) baseStart_2285303 baseEnd_2285303 := by
    simpa [prefixWord, tailWord_2285303, baseEnd_2285303] using wordTrace_append hprefix tailTrace_2285303
  have hstable : (prefixWord ++ tailWord_2285303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285303).length < 2 ^ (prefixWord ++ tailWord_2285303).sum := by decide
  have hdescent : baseEnd_2285303 < baseStart_2285303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285316 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_2285316 : Nat := 118140960795 + 2285316 * 2 ^ 59
def prefixEnd_2285316 : Nat := 4983230072969 + 3 ^ 40 * 2285316 * 2
def baseEnd_2285316 : Nat := 1173465555410485924340029

theorem tailTrace_2285316 : CollatzResearch.WordTrace tailWord_2285316 prefixEnd_2285316 1173465555410485924340029 := by
  unfold tailWord_2285316
  simp only [CollatzResearch.WordTrace]
  refine ⟨41676161094348953872233901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55568214792465271829645201 41676161094348953872233901)
  ·
    refine ⟨15628560410380857702087713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41676161094348953872233901 15628560410380857702087713)
    ·
      refine ⟨11721420307785643276565785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15628560410380857702087713 11721420307785643276565785)
      ·
        refine ⟨8791065230839232457424339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11721420307785643276565785 8791065230839232457424339)
        ·
          refine ⟨13186597846258848686136509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8791065230839232457424339 13186597846258848686136509)
          ·
            refine ⟨4944974192347068257301191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13186597846258848686136509 4944974192347068257301191)
            ·
              refine ⟨7417461288520602385951787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4944974192347068257301191 7417461288520602385951787)
              ·
                refine ⟨11126191932780903578927681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7417461288520602385951787 11126191932780903578927681)
                ·
                  refine ⟨8344643949585677684195761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11126191932780903578927681 8344643949585677684195761)
                  ·
                    refine ⟨6258482962189258263146821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8344643949585677684195761 6258482962189258263146821)
                    ·
                      refine ⟨1173465555410485924340029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6258482962189258263146821 1173465555410485924340029)
                      ·
                        rfl

theorem cell23_2285316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_2285316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285316 prefixEnd_2285316 := by exact prefixLift 2285316
  have htrace : WordTrace (prefixWord ++ tailWord_2285316) baseStart_2285316 baseEnd_2285316 := by
    simpa [prefixWord, tailWord_2285316, baseEnd_2285316] using wordTrace_append hprefix tailTrace_2285316
  have hstable : (prefixWord ++ tailWord_2285316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285316).length < 2 ^ (prefixWord ++ tailWord_2285316).sum := by decide
  have hdescent : baseEnd_2285316 < baseStart_2285316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285386 : List Nat := [3, 1, 2, 1, 1, 1, 3, 4, 3, 4]
def baseStart_2285386 : Nat := 118140960795 + 2285386 * 2 ^ 59
def prefixEnd_2285386 : Nat := 4983230072969 + 3 ^ 40 * 2285386 * 2
def baseEnd_2285386 : Nat := 391167166352100216821569

theorem tailTrace_2285386 : CollatzResearch.WordTrace tailWord_2285386 prefixEnd_2285386 391167166352100216821569 := by
  unfold tailWord_2285386
  simp only [CollatzResearch.WordTrace]
  refine ⟨20838718824611077424879003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55569916865629539799677341 20838718824611077424879003)
  ·
    refine ⟨31258078236916616137318505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20838718824611077424879003 31258078236916616137318505)
    ·
      refine ⟨23443558677687462102988879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31258078236916616137318505 23443558677687462102988879)
      ·
        refine ⟨35165338016531193154483319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23443558677687462102988879 35165338016531193154483319)
        ·
          refine ⟨52748007024796789731724979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35165338016531193154483319 52748007024796789731724979)
          ·
            refine ⟨79122010537195184597587469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52748007024796789731724979 79122010537195184597587469)
            ·
              refine ⟨29670753951448194224095301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79122010537195184597587469 29670753951448194224095301)
              ·
                refine ⟨5563266365896536417017869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29670753951448194224095301 5563266365896536417017869)
                ·
                  refine ⟨2086224887211201156381701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5563266365896536417017869 2086224887211201156381701)
                  ·
                    refine ⟨391167166352100216821569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2086224887211201156381701 391167166352100216821569)
                    ·
                      rfl

theorem cell23_2285386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_2285386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285386 prefixEnd_2285386 := by exact prefixLift 2285386
  have htrace : WordTrace (prefixWord ++ tailWord_2285386) baseStart_2285386 baseEnd_2285386 := by
    simpa [prefixWord, tailWord_2285386, baseEnd_2285386] using wordTrace_append hprefix tailTrace_2285386
  have hstable : (prefixWord ++ tailWord_2285386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285386).length < 2 ^ (prefixWord ++ tailWord_2285386).sum := by decide
  have hdescent : baseEnd_2285386 < baseStart_2285386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285416 : List Nat := [2, 1, 4, 2, 1, 1, 2, 4, 6]
def baseStart_2285416 : Nat := 118140960795 + 2285416 * 2 ^ 59
def prefixEnd_2285416 : Nat := 4983230072969 + 3 ^ 40 * 2285416 * 2
def baseEnd_2285416 : Nat := 130390767052881725898841

theorem tailTrace_2285416 : CollatzResearch.WordTrace tailWord_2285416 prefixEnd_2285416 130390767052881725898841 := by
  unfold tailWord_2285416
  simp only [CollatzResearch.WordTrace]
  refine ⟨41677984744167812411554051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55570646325557083215405401 41677984744167812411554051)
  ·
    refine ⟨62516977116251718617331077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41677984744167812411554051 62516977116251718617331077)
    ·
      refine ⟨11721933209297197240749577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62516977116251718617331077 11721933209297197240749577)
      ·
        refine ⟨8791449906972897930562183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11721933209297197240749577 8791449906972897930562183)
        ·
          refine ⟨13187174860459346895843275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8791449906972897930562183 13187174860459346895843275)
          ·
            refine ⟨19780762290689020343764913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13187174860459346895843275 19780762290689020343764913)
            ·
              refine ⟨14835571718016765257823685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19780762290689020343764913 14835571718016765257823685)
              ·
                refine ⟨2781669697128143485841941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14835571718016765257823685 2781669697128143485841941)
                ·
                  refine ⟨130390767052881725898841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2781669697128143485841941 130390767052881725898841)
                  ·
                    rfl

theorem cell23_2285416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 6].length) (baseStart_2285416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285416 prefixEnd_2285416 := by exact prefixLift 2285416
  have htrace : WordTrace (prefixWord ++ tailWord_2285416) baseStart_2285416 baseEnd_2285416 := by
    simpa [prefixWord, tailWord_2285416, baseEnd_2285416] using wordTrace_append hprefix tailTrace_2285416
  have hstable : (prefixWord ++ tailWord_2285416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285416).length < 2 ^ (prefixWord ++ tailWord_2285416).sum := by decide
  have hdescent : baseEnd_2285416 < baseStart_2285416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285493 : List Nat := [1, 3, 3, 2, 1, 3, 2, 1, 1, 6]
def baseStart_2285493 : Nat := 118140960795 + 2285493 * 2 ^ 59
def prefixEnd_2285493 : Nat := 4983230072969 + 3 ^ 40 * 2285493 * 2
def baseEnd_2285493 : Nat := 391185480495443910608905

theorem tailTrace_2285493 : CollatzResearch.WordTrace tailWord_2285493 prefixEnd_2285493 391185480495443910608905 := by
  unfold tailWord_2285493
  simp only [CollatzResearch.WordTrace]
  refine ⟨83358777909056666973661133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55572518606037777982440755 83358777909056666973661133)
  ·
    refine ⟨31259541715896250115122925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83358777909056666973661133 31259541715896250115122925)
    ·
      refine ⟨11722328143461093793171097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31259541715896250115122925 11722328143461093793171097)
      ·
        refine ⟨8791746107595820344878323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11722328143461093793171097 8791746107595820344878323)
        ·
          refine ⟨13187619161393730517317485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8791746107595820344878323 13187619161393730517317485)
          ·
            refine ⟨4945357185522648943994057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13187619161393730517317485 4945357185522648943994057)
            ·
              refine ⟨3709017889141986707995543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4945357185522648943994057 3709017889141986707995543)
              ·
                refine ⟨5563526833712980061993315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3709017889141986707995543 5563526833712980061993315)
                ·
                  refine ⟨8345290250569470092989973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5563526833712980061993315 8345290250569470092989973)
                  ·
                    refine ⟨391185480495443910608905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8345290250569470092989973 391185480495443910608905)
                    ·
                      rfl

theorem cell23_2285493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_2285493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285493 prefixEnd_2285493 := by exact prefixLift 2285493
  have htrace : WordTrace (prefixWord ++ tailWord_2285493) baseStart_2285493 baseEnd_2285493 := by
    simpa [prefixWord, tailWord_2285493, baseEnd_2285493] using wordTrace_append hprefix tailTrace_2285493
  have hstable : (prefixWord ++ tailWord_2285493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285493).length < 2 ^ (prefixWord ++ tailWord_2285493).sum := by decide
  have hdescent : baseEnd_2285493 < baseStart_2285493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285503 : List Nat := [1, 1, 2, 2, 2, 1, 4, 4, 1, 2, 3]
def baseStart_2285503 : Nat := 118140960795 + 2285503 * 2 ^ 59
def prefixEnd_2285503 : Nat := 4983230072969 + 3 ^ 40 * 2285503 * 2
def baseEnd_2285503 : Nat := 1173561576292876692701669

theorem tailTrace_2285503 : CollatzResearch.WordTrace tailWord_2285503 prefixEnd_2285503 1173561576292876692701669 := by
  unfold tailWord_2285503
  simp only [CollatzResearch.WordTrace]
  refine ⟨83359142639020438681525163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55572761759346959121016775 83359142639020438681525163)
  ·
    refine ⟨125038713958530658022287745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83359142639020438681525163 125038713958530658022287745)
    ·
      refine ⟨93779035468897993516715809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125038713958530658022287745 93779035468897993516715809)
      ·
        refine ⟨70334276601673495137536857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93779035468897993516715809 70334276601673495137536857)
        ·
          refine ⟨52750707451255121353152643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70334276601673495137536857 52750707451255121353152643)
          ·
            refine ⟨79126061176882682029728965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52750707451255121353152643 79126061176882682029728965)
            ·
              refine ⟨14836136470665502880574181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79126061176882682029728965 14836136470665502880574181)
              ·
                refine ⟨2781775588249781790107659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14836136470665502880574181 2781775588249781790107659)
                ·
                  refine ⟨4172663382374672685161489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2781775588249781790107659 4172663382374672685161489)
                  ·
                    refine ⟨3129497536781004513871117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4172663382374672685161489 3129497536781004513871117)
                    ·
                      refine ⟨1173561576292876692701669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3129497536781004513871117 1173561576292876692701669)
                      ·
                        rfl

theorem cell23_2285503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 2, 3].length) (baseStart_2285503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285503 prefixEnd_2285503 := by exact prefixLift 2285503
  have htrace : WordTrace (prefixWord ++ tailWord_2285503) baseStart_2285503 baseEnd_2285503 := by
    simpa [prefixWord, tailWord_2285503, baseEnd_2285503] using wordTrace_append hprefix tailTrace_2285503
  have hstable : (prefixWord ++ tailWord_2285503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285503).length < 2 ^ (prefixWord ++ tailWord_2285503).sum := by decide
  have hdescent : baseEnd_2285503 < baseStart_2285503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285520 : List Nat := [2, 1, 1, 1, 1, 2, 8, 1, 1, 2, 3]
def baseStart_2285520 : Nat := 118140960795 + 2285520 * 2 ^ 59
def prefixEnd_2285520 : Nat := 4983230072969 + 3 ^ 40 * 2285520 * 2
def baseEnd_2285520 : Nat := 1173570305464003126189091

theorem tailTrace_2285520 : CollatzResearch.WordTrace tailWord_2285520 prefixEnd_2285520 1173570305464003126189091 := by
  unfold tailWord_2285520
  simp only [CollatzResearch.WordTrace]
  refine ⟨41679881339979425292447007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55573175119972567056596009 41679881339979425292447007)
  ·
    refine ⟨62519822009969137938670511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41679881339979425292447007 62519822009969137938670511)
    ·
      refine ⟨93779733014953706908005767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62519822009969137938670511 93779733014953706908005767)
      ·
        refine ⟨140669599522430560362008651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93779733014953706908005767 140669599522430560362008651)
        ·
          refine ⟨211004399283645840543012977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140669599522430560362008651 211004399283645840543012977)
          ·
            refine ⟨158253299462734380407259733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211004399283645840543012977 158253299462734380407259733)
            ·
              refine ⟨1854530853078918520397575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 158253299462734380407259733 1854530853078918520397575)
              ·
                refine ⟨2781796279618377780596363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854530853078918520397575 2781796279618377780596363)
                ·
                  refine ⟨4172694419427566670894545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2781796279618377780596363 4172694419427566670894545)
                  ·
                    refine ⟨3129520814570675003170909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4172694419427566670894545 3129520814570675003170909)
                    ·
                      refine ⟨1173570305464003126189091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3129520814570675003170909 1173570305464003126189091)
                      ·
                        rfl

theorem cell23_2285520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 1, 2, 3].length) (baseStart_2285520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285520 prefixEnd_2285520 := by exact prefixLift 2285520
  have htrace : WordTrace (prefixWord ++ tailWord_2285520) baseStart_2285520 baseEnd_2285520 := by
    simpa [prefixWord, tailWord_2285520, baseEnd_2285520] using wordTrace_append hprefix tailTrace_2285520
  have hstable : (prefixWord ++ tailWord_2285520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285520).length < 2 ^ (prefixWord ++ tailWord_2285520).sum := by decide
  have hdescent : baseEnd_2285520 < baseStart_2285520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285550 : List Nat := [4, 1, 2, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_2285550 : Nat := 118140960795 + 2285550 * 2 ^ 59
def prefixEnd_2285550 : Nat := 4983230072969 + 3 ^ 40 * 2285550 * 2
def baseEnd_2285550 : Nat := 1173585709883638008813953

theorem tailTrace_2285550 : CollatzResearch.WordTrace tailWord_2285550 prefixEnd_2285550 1173585709883638008813953 := by
  unfold tailWord_2285550
  simp only [CollatzResearch.WordTrace]
  refine ⟨10420107108731270713560763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55573904579900110472324069 10420107108731270713560763)
  ·
    refine ⟨15630160663096906070341145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10420107108731270713560763 15630160663096906070341145)
    ·
      refine ⟨11722620497322679552755859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15630160663096906070341145 11722620497322679552755859)
      ·
        refine ⟨17583930745984019329133789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11722620497322679552755859 17583930745984019329133789)
        ·
          refine ⟨6593974029744007248425171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17583930745984019329133789 6593974029744007248425171)
          ·
            refine ⟨9890961044616010872637757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6593974029744007248425171 9890961044616010872637757)
            ·
              refine ⟨3709110391731004077239159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9890961044616010872637757 3709110391731004077239159)
              ·
                refine ⟨5563665587596506115858739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3709110391731004077239159 5563665587596506115858739)
                ·
                  refine ⟨8345498381394759173788109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5563665587596506115858739 8345498381394759173788109)
                  ·
                    refine ⟨3129561893023034690170541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8345498381394759173788109 3129561893023034690170541)
                    ·
                      refine ⟨1173585709883638008813953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3129561893023034690170541 1173585709883638008813953)
                      ·
                        rfl

theorem cell23_2285550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_2285550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285550 prefixEnd_2285550 := by exact prefixLift 2285550
  have htrace : WordTrace (prefixWord ++ tailWord_2285550) baseStart_2285550 baseEnd_2285550 := by
    simpa [prefixWord, tailWord_2285550, baseEnd_2285550] using wordTrace_append hprefix tailTrace_2285550
  have hstable : (prefixWord ++ tailWord_2285550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285550).length < 2 ^ (prefixWord ++ tailWord_2285550).sum := by decide
  have hdescent : baseEnd_2285550 < baseStart_2285550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285560 : List Nat := [2, 1, 2, 1, 1, 3, 3, 4, 1, 3, 2]
def baseStart_2285560 : Nat := 118140960795 + 2285560 * 2 ^ 59
def prefixEnd_2285560 : Nat := 4983230072969 + 3 ^ 40 * 2285560 * 2
def baseEnd_2285560 : Nat := 1173590844690182969688907

theorem tailTrace_2285560 : CollatzResearch.WordTrace tailWord_2285560 prefixEnd_2285560 1173590844690182969688907 := by
  unfold tailWord_2285560
  simp only [CollatzResearch.WordTrace]
  refine ⟨41680610799906968708175067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55574147733209291610900089 41680610799906968708175067)
  ·
    refine ⟨62520916199860453062262601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41680610799906968708175067 62520916199860453062262601)
    ·
      refine ⟨46890687149895339796696951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62520916199860453062262601 46890687149895339796696951)
      ·
        refine ⟨70336030724843009695045427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46890687149895339796696951 70336030724843009695045427)
        ·
          refine ⟨105504046087264514542568141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70336030724843009695045427 105504046087264514542568141)
          ·
            refine ⟨39564017282724192953463053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105504046087264514542568141 39564017282724192953463053)
            ·
              refine ⟨14836506481021572357548645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39564017282724192953463053 14836506481021572357548645)
              ·
                refine ⟨2781844965191544817040371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14836506481021572357548645 2781844965191544817040371)
                ·
                  refine ⟨4172767447787317225560557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2781844965191544817040371 4172767447787317225560557)
                  ·
                    refine ⟨1564787792920243959585209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4172767447787317225560557 1564787792920243959585209)
                    ·
                      refine ⟨1173590844690182969688907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1564787792920243959585209 1173590844690182969688907)
                      ·
                        rfl

theorem cell23_2285560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 1, 3, 2].length) (baseStart_2285560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285560 prefixEnd_2285560 := by exact prefixLift 2285560
  have htrace : WordTrace (prefixWord ++ tailWord_2285560) baseStart_2285560 baseEnd_2285560 := by
    simpa [prefixWord, tailWord_2285560, baseEnd_2285560] using wordTrace_append hprefix tailTrace_2285560
  have hstable : (prefixWord ++ tailWord_2285560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285560).length < 2 ^ (prefixWord ++ tailWord_2285560).sum := by decide
  have hdescent : baseEnd_2285560 < baseStart_2285560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285574 : List Nat := [6, 2, 1, 2, 1, 2, 9]
def baseStart_2285574 : Nat := 118140960795 + 2285574 * 2 ^ 59
def prefixEnd_2285574 : Nat := 4983230072969 + 3 ^ 40 * 2285574 * 2
def baseEnd_2285574 : Nat := 14488864610115381665603

theorem tailTrace_2285574 : CollatzResearch.WordTrace tailWord_2285574 prefixEnd_2285574 14488864610115381665603 := by
  unfold tailWord_2285574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2605054131930100556479993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55574488147842145204906517 2605054131930100556479993)
  ·
    refine ⟨1953790598947575417359995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2605054131930100556479993 1953790598947575417359995)
    ·
      refine ⟨2930685898421363126039993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1953790598947575417359995 2930685898421363126039993)
      ·
        refine ⟨2198014423816022344529995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2930685898421363126039993 2198014423816022344529995)
        ·
          refine ⟨3297021635724033516794993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2198014423816022344529995 3297021635724033516794993)
          ·
            refine ⟨2472766226793025137596245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3297021635724033516794993 2472766226793025137596245)
            ·
              refine ⟨14488864610115381665603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2472766226793025137596245 14488864610115381665603)
              ·
                rfl

theorem cell23_2285574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 9].length) (baseStart_2285574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285574 prefixEnd_2285574 := by exact prefixLift 2285574
  have htrace : WordTrace (prefixWord ++ tailWord_2285574) baseStart_2285574 baseEnd_2285574 := by
    simpa [prefixWord, tailWord_2285574, baseEnd_2285574] using wordTrace_append hprefix tailTrace_2285574
  have hstable : (prefixWord ++ tailWord_2285574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285574).length < 2 ^ (prefixWord ++ tailWord_2285574).sum := by decide
  have hdescent : baseEnd_2285574 < baseStart_2285574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285601 : List Nat := [1, 2, 3, 2, 5, 1, 2, 1, 2, 1, 3]
def baseStart_2285601 : Nat := 118140960795 + 2285601 * 2 ^ 59
def prefixEnd_2285601 : Nat := 4983230072969 + 3 ^ 40 * 2285601 * 2
def baseEnd_2285601 : Nat := 1173611897397017309276219

theorem tailTrace_2285601 : CollatzResearch.WordTrace tailWord_2285601 prefixEnd_2285601 1173611897397017309276219 := by
  unfold tailWord_2285601
  simp only [CollatzResearch.WordTrace]
  refine ⟨83362716992665401418592657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55575144661776934279061771 83362716992665401418592657)
  ·
    refine ⟨62522037744499051063944493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83362716992665401418592657 62522037744499051063944493)
    ·
      refine ⟨23445764154187144148979185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62522037744499051063944493 23445764154187144148979185)
      ·
        refine ⟨17584323115640358111734389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23445764154187144148979185 17584323115640358111734389)
        ·
          refine ⟨1648530292091283572975099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17584323115640358111734389 1648530292091283572975099)
          ·
            refine ⟨2472795438136925359462649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1648530292091283572975099 2472795438136925359462649)
            ·
              refine ⟨1854596578602694019596987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2472795438136925359462649 1854596578602694019596987)
              ·
                refine ⟨2781894867904041029395481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854596578602694019596987 2781894867904041029395481)
                ·
                  refine ⟨2086421150928030772046611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2781894867904041029395481 2086421150928030772046611)
                  ·
                    refine ⟨3129631726392046158069917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2086421150928030772046611 3129631726392046158069917)
                    ·
                      refine ⟨1173611897397017309276219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3129631726392046158069917 1173611897397017309276219)
                      ·
                        rfl

theorem cell23_2285601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_2285601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285601 prefixEnd_2285601 := by exact prefixLift 2285601
  have htrace : WordTrace (prefixWord ++ tailWord_2285601) baseStart_2285601 baseEnd_2285601 := by
    simpa [prefixWord, tailWord_2285601, baseEnd_2285601] using wordTrace_append hprefix tailTrace_2285601
  have hstable : (prefixWord ++ tailWord_2285601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285601).length < 2 ^ (prefixWord ++ tailWord_2285601).sum := by decide
  have hdescent : baseEnd_2285601 < baseStart_2285601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285653 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_2285653 : Nat := 118140960795 + 2285653 * 2 ^ 59
def prefixEnd_2285653 : Nat := 4983230072969 + 3 ^ 40 * 2285653 * 2
def baseEnd_2285653 : Nat := 1173638598391051105825979

theorem tailTrace_2285653 : CollatzResearch.WordTrace tailWord_2285653 prefixEnd_2285653 1173638598391051105825979 := by
  unfold tailWord_2285653
  simp only [CollatzResearch.WordTrace]
  refine ⟨83364613588477014299485613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55576409058984676199657075 83364613588477014299485613)
  ·
    refine ⟨31261730095678880362307105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83364613588477014299485613 31261730095678880362307105)
    ·
      refine ⟨23446297571759160271730329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31261730095678880362307105 23446297571759160271730329)
      ·
        refine ⟨17584723178819370203797747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23446297571759160271730329 17584723178819370203797747)
        ·
          refine ⟨26377084768229055305696621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17584723178819370203797747 26377084768229055305696621)
          ·
            refine ⟨9891406788085895739636233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26377084768229055305696621 9891406788085895739636233)
            ·
              refine ⟨7418555091064421804727175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9891406788085895739636233 7418555091064421804727175)
              ·
                refine ⟨11127832636596632707090763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7418555091064421804727175 11127832636596632707090763)
                ·
                  refine ⟨16691748954894949060636145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11127832636596632707090763 16691748954894949060636145)
                  ·
                    refine ⟨12518811716171211795477109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16691748954894949060636145 12518811716171211795477109)
                    ·
                      refine ⟨1173638598391051105825979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12518811716171211795477109 1173638598391051105825979)
                      ·
                        rfl

theorem cell23_2285653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_2285653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285653 prefixEnd_2285653 := by exact prefixLift 2285653
  have htrace : WordTrace (prefixWord ++ tailWord_2285653) baseStart_2285653 baseEnd_2285653 := by
    simpa [prefixWord, tailWord_2285653, baseEnd_2285653] using wordTrace_append hprefix tailTrace_2285653
  have hstable : (prefixWord ++ tailWord_2285653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285653).length < 2 ^ (prefixWord ++ tailWord_2285653).sum := by decide
  have hdescent : baseEnd_2285653 < baseStart_2285653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285680 : List Nat := [2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 4]
def baseStart_2285680 : Nat := 118140960795 + 2285680 * 2 ^ 59
def prefixEnd_2285680 : Nat := 4983230072969 + 3 ^ 40 * 2285680 * 2
def baseEnd_2285680 : Nat := 1173652462368722500188355

theorem tailTrace_2285680 : CollatzResearch.WordTrace tailWord_2285680 prefixEnd_2285680 1173652462368722500188355 := by
  unfold tailWord_2285680
  simp only [CollatzResearch.WordTrace]
  refine ⟨41682799179689598955359247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55577065572919465273812329 41682799179689598955359247)
  ·
    refine ⟨62524198769534398433038871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41682799179689598955359247 62524198769534398433038871)
    ·
      refine ⟨93786298154301597649558307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62524198769534398433038871 93786298154301597649558307)
      ·
        refine ⟨140679447231452396474337461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93786298154301597649558307 140679447231452396474337461)
        ·
          refine ⟨13188698177948662169469137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140679447231452396474337461 13188698177948662169469137)
          ·
            refine ⟨9891523633461496627101853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13188698177948662169469137 9891523633461496627101853)
            ·
              refine ⟨3709321362548061235163195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9891523633461496627101853 3709321362548061235163195)
              ·
                refine ⟨5563982043822091852744793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3709321362548061235163195 5563982043822091852744793)
                ·
                  refine ⟨4172986532866568889558595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5563982043822091852744793 4172986532866568889558595)
                  ·
                    refine ⟨6259479799299853334337893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4172986532866568889558595 6259479799299853334337893)
                    ·
                      refine ⟨1173652462368722500188355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6259479799299853334337893 1173652462368722500188355)
                      ·
                        rfl

theorem cell23_2285680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 4].length) (baseStart_2285680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285680 prefixEnd_2285680 := by exact prefixLift 2285680
  have htrace : WordTrace (prefixWord ++ tailWord_2285680) baseStart_2285680 baseEnd_2285680 := by
    simpa [prefixWord, tailWord_2285680, baseEnd_2285680] using wordTrace_append hprefix tailTrace_2285680
  have hstable : (prefixWord ++ tailWord_2285680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285680).length < 2 ^ (prefixWord ++ tailWord_2285680).sum := by decide
  have hdescent : baseEnd_2285680 < baseStart_2285680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285693 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_2285693 : Nat := 118140960795 + 2285693 * 2 ^ 59
def prefixEnd_2285693 : Nat := 4983230072969 + 3 ^ 40 * 2285693 * 2
def baseEnd_2285693 : Nat := 1173659137617230949325795

theorem tailTrace_2285693 : CollatzResearch.WordTrace tailWord_2285693 prefixEnd_2285693 1173659137617230949325795 := by
  unfold tailWord_2285693
  simp only [CollatzResearch.WordTrace]
  refine ⟨83366072508332101130941733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55577381672221400753961155 83366072508332101130941733)
  ·
    refine ⟨15631138595312268962051575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83366072508332101130941733 15631138595312268962051575)
    ·
      refine ⟨23446707892968403443077363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15631138595312268962051575 23446707892968403443077363)
      ·
        refine ⟨35170061839452605164616045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23446707892968403443077363 35170061839452605164616045)
        ·
          refine ⟨13188773189794726936731017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35170061839452605164616045 13188773189794726936731017)
          ·
            refine ⟨9891579892346045202548263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13188773189794726936731017 9891579892346045202548263)
            ·
              refine ⟨14837369838519067803822395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9891579892346045202548263 14837369838519067803822395)
              ·
                refine ⟨22256054757778601705733593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14837369838519067803822395 22256054757778601705733593)
                ·
                  refine ⟨16692041068333951279300195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22256054757778601705733593 16692041068333951279300195)
                  ·
                    refine ⟨25038061602500926918950293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16692041068333951279300195 25038061602500926918950293)
                    ·
                      refine ⟨1173659137617230949325795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25038061602500926918950293 1173659137617230949325795)
                      ·
                        rfl

theorem cell23_2285693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_2285693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285693 prefixEnd_2285693 := by exact prefixLift 2285693
  have htrace : WordTrace (prefixWord ++ tailWord_2285693) baseStart_2285693 baseEnd_2285693 := by
    simpa [prefixWord, tailWord_2285693, baseEnd_2285693] using wordTrace_append hprefix tailTrace_2285693
  have hstable : (prefixWord ++ tailWord_2285693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285693).length < 2 ^ (prefixWord ++ tailWord_2285693).sum := by decide
  have hdescent : baseEnd_2285693 < baseStart_2285693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285700 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_2285700 : Nat := 118140960795 + 2285700 * 2 ^ 59
def prefixEnd_2285700 : Nat := 4983230072969 + 3 ^ 40 * 2285700 * 2
def baseEnd_2285700 : Nat := 1173662731981812421938263

theorem tailTrace_2285700 : CollatzResearch.WordTrace tailWord_2285700 prefixEnd_2285700 1173662731981812421938263 := by
  unfold tailWord_2285700
  simp only [CollatzResearch.WordTrace]
  refine ⟨41683163909653370663223277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55577551879537827550964369 41683163909653370663223277)
  ·
    refine ⟨15631186466120013998708729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41683163909653370663223277 15631186466120013998708729)
    ·
      refine ⟨11723389849590010499031547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15631186466120013998708729 11723389849590010499031547)
      ·
        refine ⟨17585084774385015748547321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11723389849590010499031547 17585084774385015748547321)
        ·
          refine ⟨13188813580788761811410491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17585084774385015748547321 13188813580788761811410491)
          ·
            refine ⟨19783220371183142717115737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13188813580788761811410491 19783220371183142717115737)
            ·
              refine ⟨14837415278387357037836803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19783220371183142717115737 14837415278387357037836803)
              ·
                refine ⟨22256122917581035556755205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14837415278387357037836803 22256122917581035556755205)
                ·
                  refine ⟨4173023047046444166891601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22256122917581035556755205 4173023047046444166891601)
                  ·
                    refine ⟨3129767285284833125168701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4173023047046444166891601 3129767285284833125168701)
                    ·
                      refine ⟨1173662731981812421938263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3129767285284833125168701 1173662731981812421938263)
                      ·
                        rfl

theorem cell23_2285700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_2285700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285700 prefixEnd_2285700 := by exact prefixLift 2285700
  have htrace : WordTrace (prefixWord ++ tailWord_2285700) baseStart_2285700 baseEnd_2285700 := by
    simpa [prefixWord, tailWord_2285700, baseEnd_2285700] using wordTrace_append hprefix tailTrace_2285700
  have hstable : (prefixWord ++ tailWord_2285700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285700).length < 2 ^ (prefixWord ++ tailWord_2285700).sum := by decide
  have hdescent : baseEnd_2285700 < baseStart_2285700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285741 : List Nat := [1, 5, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_2285741 : Nat := 118140960795 + 2285741 * 2 ^ 59
def prefixEnd_2285741 : Nat := 4983230072969 + 3 ^ 40 * 2285741 * 2
def baseEnd_2285741 : Nat := 391227928229548920508525

theorem tailTrace_2285741 : CollatzResearch.WordTrace tailWord_2285741 prefixEnd_2285741 391227928229548920508525 := by
  unfold tailWord_2285741
  simp only [CollatzResearch.WordTrace]
  refine ⟨83367823212158205328689077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55578548808105470219126051 83367823212158205328689077)
  ·
    refine ⟨7815733426139831749564601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83367823212158205328689077 7815733426139831749564601)
    ·
      refine ⟨5861800069604873812173451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7815733426139831749564601 5861800069604873812173451)
      ·
        refine ⟨8792700104407310718260177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5861800069604873812173451 8792700104407310718260177)
        ·
          refine ⟨6594525078305483038695133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8792700104407310718260177 6594525078305483038695133)
          ·
            refine ⟨2472946904364556139510675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6594525078305483038695133 2472946904364556139510675)
            ·
              refine ⟨3709420356546834209266013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2472946904364556139510675 3709420356546834209266013)
              ·
                refine ⟨1391032633705062828474755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3709420356546834209266013 1391032633705062828474755)
                ·
                  refine ⟨2086548950557594242712133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391032633705062828474755 2086548950557594242712133)
                  ·
                    refine ⟨391227928229548920508525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2086548950557594242712133 391227928229548920508525)
                    ·
                      rfl

theorem cell23_2285741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_2285741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285741 prefixEnd_2285741 := by exact prefixLift 2285741
  have htrace : WordTrace (prefixWord ++ tailWord_2285741) baseStart_2285741 baseEnd_2285741 := by
    simpa [prefixWord, tailWord_2285741, baseEnd_2285741] using wordTrace_append hprefix tailTrace_2285741
  have hstable : (prefixWord ++ tailWord_2285741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285741).length < 2 ^ (prefixWord ++ tailWord_2285741).sum := by decide
  have hdescent : baseEnd_2285741 < baseStart_2285741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285764 : List Nat := [2, 3, 3, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_2285764 : Nat := 118140960795 + 2285764 * 2 ^ 59
def prefixEnd_2285764 : Nat := 4983230072969 + 3 ^ 40 * 2285764 * 2
def baseEnd_2285764 : Nat := 1173695594743700171537969

theorem tailTrace_2285764 : CollatzResearch.WordTrace tailWord_2285764 prefixEnd_2285764 1173695594743700171537969 := by
  unfold tailWord_2285764
  simp only [CollatzResearch.WordTrace]
  refine ⟨41684331045537440128388173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55579108060716586837850897 41684331045537440128388173)
  ·
    refine ⟨15631624142076540048145565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41684331045537440128388173 15631624142076540048145565)
    ·
      refine ⟨5861859053278702518054587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15631624142076540048145565 5861859053278702518054587)
      ·
        refine ⟨8792788579918053777081881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5861859053278702518054587 8792788579918053777081881)
        ·
          refine ⟨6594591434938540332811411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8792788579918053777081881 6594591434938540332811411)
          ·
            refine ⟨9891887152407810499217117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6594591434938540332811411 9891887152407810499217117)
            ·
              refine ⟨3709457682152928937206419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9891887152407810499217117 3709457682152928937206419)
              ·
                refine ⟨5564186523229393405809629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3709457682152928937206419 5564186523229393405809629)
                ·
                  refine ⟨2086569946211022527178611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5564186523229393405809629 2086569946211022527178611)
                  ·
                    refine ⟨3129854919316533790767917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2086569946211022527178611 3129854919316533790767917)
                    ·
                      refine ⟨1173695594743700171537969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3129854919316533790767917 1173695594743700171537969)
                      ·
                        rfl

theorem cell23_2285764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_2285764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285764 prefixEnd_2285764 := by exact prefixLift 2285764
  have htrace : WordTrace (prefixWord ++ tailWord_2285764) baseStart_2285764 baseEnd_2285764 := by
    simpa [prefixWord, tailWord_2285764, baseEnd_2285764] using wordTrace_append hprefix tailTrace_2285764
  have hstable : (prefixWord ++ tailWord_2285764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285764).length < 2 ^ (prefixWord ++ tailWord_2285764).sum := by decide
  have hdescent : baseEnd_2285764 < baseStart_2285764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285770 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_2285770 : Nat := 118140960795 + 2285770 * 2 ^ 59
def prefixEnd_2285770 : Nat := 4983230072969 + 3 ^ 40 * 2285770 * 2
def baseEnd_2285770 : Nat := 1173698675627627148062941

theorem tailTrace_2285770 : CollatzResearch.WordTrace tailWord_2285770 prefixEnd_2285770 1173698675627627148062941 := by
  unfold tailWord_2285770
  simp only [CollatzResearch.WordTrace]
  refine ⟨20842220232263285820373691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55579253952702095520996509 20842220232263285820373691)
  ·
    refine ⟨31263330348394928730560537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20842220232263285820373691 31263330348394928730560537)
    ·
      refine ⟨23447497761296196547920403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31263330348394928730560537 23447497761296196547920403)
      ·
        refine ⟨35171246641944294821880605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23447497761296196547920403 35171246641944294821880605)
        ·
          refine ⟨13189217490729110558205227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35171246641944294821880605 13189217490729110558205227)
          ·
            refine ⟨19783826236093665837307841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13189217490729110558205227 19783826236093665837307841)
            ·
              refine ⟨14837869677070249377980881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19783826236093665837307841 14837869677070249377980881)
              ·
                refine ⟨11128402257802687033485661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14837869677070249377980881 11128402257802687033485661)
                ·
                  refine ⟨4173150846676007637557123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11128402257802687033485661 4173150846676007637557123)
                  ·
                    refine ⟨6259726270014011456335685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4173150846676007637557123 6259726270014011456335685)
                    ·
                      refine ⟨1173698675627627148062941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6259726270014011456335685 1173698675627627148062941)
                      ·
                        rfl

theorem cell23_2285770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_2285770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285770 prefixEnd_2285770 := by exact prefixLift 2285770
  have htrace : WordTrace (prefixWord ++ tailWord_2285770) baseStart_2285770 baseEnd_2285770 := by
    simpa [prefixWord, tailWord_2285770, baseEnd_2285770] using wordTrace_append hprefix tailTrace_2285770
  have hstable : (prefixWord ++ tailWord_2285770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285770).length < 2 ^ (prefixWord ++ tailWord_2285770).sum := by decide
  have hdescent : baseEnd_2285770 < baseStart_2285770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285793 : List Nat := [1, 2, 3, 1, 3, 1, 1, 11]
def baseStart_2285793 : Nat := 118140960795 + 2285793 * 2 ^ 59
def prefixEnd_2285793 : Nat := 4983230072969 + 3 ^ 40 * 2285793 * 2
def baseEnd_2285793 : Nat := 43470758728988168817605

theorem tailTrace_2285793 : CollatzResearch.WordTrace tailWord_2285793 prefixEnd_2285793 43470758728988168817605 := by
  unfold tailWord_2285793
  simp only [CollatzResearch.WordTrace]
  refine ⟨83369719807969818209582033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55579813205313212139721355 83369719807969818209582033)
  ·
    refine ⟨62527289855977363657186525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83369719807969818209582033 62527289855977363657186525)
    ·
      refine ⟨23447733695991511371444947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62527289855977363657186525 23447733695991511371444947)
      ·
        refine ⟨35171600543987267057167421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23447733695991511371444947 35171600543987267057167421)
        ·
          refine ⟨13189350203995225146437783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35171600543987267057167421 13189350203995225146437783)
          ·
            refine ⟨19784025305992837719656675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13189350203995225146437783 19784025305992837719656675)
            ·
              refine ⟨29676037958989256579485013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19784025305992837719656675 29676037958989256579485013)
              ·
                refine ⟨43470758728988168817605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 29676037958989256579485013 43470758728988168817605)
                ·
                  rfl

theorem cell23_2285793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 11].length) (baseStart_2285793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285793 prefixEnd_2285793 := by exact prefixLift 2285793
  have htrace : WordTrace (prefixWord ++ tailWord_2285793) baseStart_2285793 baseEnd_2285793 := by
    simpa [prefixWord, tailWord_2285793, baseEnd_2285793] using wordTrace_append hprefix tailTrace_2285793
  have hstable : (prefixWord ++ tailWord_2285793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285793).length < 2 ^ (prefixWord ++ tailWord_2285793).sum := by decide
  have hdescent : baseEnd_2285793 < baseStart_2285793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285800 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_2285800 : Nat := 118140960795 + 2285800 * 2 ^ 59
def prefixEnd_2285800 : Nat := 4983230072969 + 3 ^ 40 * 2285800 * 2
def baseEnd_2285800 : Nat := 1173714080047262030687803

theorem tailTrace_2285800 : CollatzResearch.WordTrace tailWord_2285800 prefixEnd_2285800 1173714080047262030687803 := by
  unfold tailWord_2285800
  simp only [CollatzResearch.WordTrace]
  refine ⟨41684987559472229202543427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55579983412629638936724569 41684987559472229202543427)
  ·
    refine ⟨62527481339208343803815141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41684987559472229202543427 62527481339208343803815141)
    ·
      refine ⟨11723902751101564463215339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62527481339208343803815141 11723902751101564463215339)
      ·
        refine ⟨17585854126652346694823009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11723902751101564463215339 17585854126652346694823009)
        ·
          refine ⟨13189390594989260021117257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17585854126652346694823009 13189390594989260021117257)
          ·
            refine ⟨9892042946241945015837943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13189390594989260021117257 9892042946241945015837943)
            ·
              refine ⟨14838064419362917523756915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9892042946241945015837943 14838064419362917523756915)
              ·
                refine ⟨22257096629044376285635373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14838064419362917523756915 22257096629044376285635373)
                ·
                  refine ⟨8346411235891641107113265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22257096629044376285635373 8346411235891641107113265)
                  ·
                    refine ⟨6259808426918730830334949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8346411235891641107113265 6259808426918730830334949)
                    ·
                      refine ⟨1173714080047262030687803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6259808426918730830334949 1173714080047262030687803)
                      ·
                        rfl

theorem cell23_2285800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_2285800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285800 prefixEnd_2285800 := by exact prefixLift 2285800
  have htrace : WordTrace (prefixWord ++ tailWord_2285800) baseStart_2285800 baseEnd_2285800 := by
    simpa [prefixWord, tailWord_2285800, baseEnd_2285800] using wordTrace_append hprefix tailTrace_2285800
  have hstable : (prefixWord ++ tailWord_2285800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285800).length < 2 ^ (prefixWord ++ tailWord_2285800).sum := by decide
  have hdescent : baseEnd_2285800 < baseStart_2285800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285807 : List Nat := [1, 1, 2, 1, 6, 3, 1, 1, 1, 1, 5]
def baseStart_2285807 : Nat := 118140960795 + 2285807 * 2 ^ 59
def prefixEnd_2285807 : Nat := 4983230072969 + 3 ^ 40 * 2285807 * 2
def baseEnd_2285807 : Nat := 1173717674411843503300271

theorem tailTrace_2285807 : CollatzResearch.WordTrace tailWord_2285807 prefixEnd_2285807 1173717674411843503300271 := by
  unfold tailWord_2285807
  simp only [CollatzResearch.WordTrace]
  refine ⟨83370230429919098600591675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55580153619946065733727783 83370230429919098600591675)
  ·
    refine ⟨125055345644878647900887513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83370230429919098600591675 125055345644878647900887513)
    ·
      refine ⟨93791509233658985925665635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125055345644878647900887513 93791509233658985925665635)
      ·
        refine ⟨140687263850488478888498453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93791509233658985925665635 140687263850488478888498453)
        ·
          refine ⟨6594715492991647447898365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 140687263850488478888498453 6594715492991647447898365)
          ·
            refine ⟨2473018309871867792961887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6594715492991647447898365 2473018309871867792961887)
            ·
              refine ⟨3709527464807801689442831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2473018309871867792961887 3709527464807801689442831)
              ·
                refine ⟨5564291197211702534164247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3709527464807801689442831 5564291197211702534164247)
                ·
                  refine ⟨8346436795817553801246371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5564291197211702534164247 8346436795817553801246371)
                  ·
                    refine ⟨12519655193726330701869557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8346436795817553801246371 12519655193726330701869557)
                    ·
                      refine ⟨1173717674411843503300271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12519655193726330701869557 1173717674411843503300271)
                      ·
                        rfl

theorem cell23_2285807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 1, 5].length) (baseStart_2285807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285807 prefixEnd_2285807 := by exact prefixLift 2285807
  have htrace : WordTrace (prefixWord ++ tailWord_2285807) baseStart_2285807 baseEnd_2285807 := by
    simpa [prefixWord, tailWord_2285807, baseEnd_2285807] using wordTrace_append hprefix tailTrace_2285807
  have hstable : (prefixWord ++ tailWord_2285807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285807).length < 2 ^ (prefixWord ++ tailWord_2285807).sum := by decide
  have hdescent : baseEnd_2285807 < baseStart_2285807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285823 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 1, 9]
def baseStart_2285823 : Nat := 118140960795 + 2285823 * 2 ^ 59
def prefixEnd_2285823 : Nat := 4983230072969 + 3 ^ 40 * 2285823 * 2
def baseEnd_2285823 : Nat := 391241963367438480233399

theorem tailTrace_2285823 : CollatzResearch.WordTrace tailWord_2285823 prefixEnd_2285823 391241963367438480233399 := by
  unfold tailWord_2285823
  simp only [CollatzResearch.WordTrace]
  refine ⟨83370813997861133333174123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55580542665240755555449415 83370813997861133333174123)
  ·
    refine ⟨125056220996791699999761185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83370813997861133333174123 125056220996791699999761185)
    ·
      refine ⟨93792165747593774999820889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125056220996791699999761185 93792165747593774999820889)
      ·
        refine ⟨70344124310695331249865667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93792165747593774999820889 70344124310695331249865667)
        ·
          refine ⟨105516186466042996874798501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70344124310695331249865667 105516186466042996874798501)
          ·
            refine ⟨19784284962383061914024719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105516186466042996874798501 19784284962383061914024719)
            ·
              refine ⟨29676427443574592871037079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19784284962383061914024719 29676427443574592871037079)
              ·
                refine ⟨44514641165361889306555619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29676427443574592871037079 44514641165361889306555619)
                ·
                  refine ⟨66771961748042833959833429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44514641165361889306555619 66771961748042833959833429)
                  ·
                    refine ⟨391241963367438480233399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 66771961748042833959833429 391241963367438480233399)
                    ·
                      rfl

theorem cell23_2285823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 9].length) (baseStart_2285823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285823 prefixEnd_2285823 := by exact prefixLift 2285823
  have htrace : WordTrace (prefixWord ++ tailWord_2285823) baseStart_2285823 baseEnd_2285823 := by
    simpa [prefixWord, tailWord_2285823, baseEnd_2285823] using wordTrace_append hprefix tailTrace_2285823
  have hstable : (prefixWord ++ tailWord_2285823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285823).length < 2 ^ (prefixWord ++ tailWord_2285823).sum := by decide
  have hdescent : baseEnd_2285823 < baseStart_2285823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285880 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 1, 6, 3]
def baseStart_2285880 : Nat := 118140960795 + 2285880 * 2 ^ 59
def prefixEnd_2285880 : Nat := 4983230072969 + 3 ^ 40 * 2285880 * 2
def baseEnd_2285880 : Nat := 1173755158499621717687435

theorem tailTrace_2285880 : CollatzResearch.WordTrace tailWord_2285880 prefixEnd_2285880 1173755158499621717687435 := by
  unfold tailWord_2285880
  simp only [CollatzResearch.WordTrace]
  refine ⟨41686446479327316033999547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55581928639103088045332729 41686446479327316033999547)
  ·
    refine ⟨62529669718990974050999321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41686446479327316033999547 62529669718990974050999321)
    ·
      refine ⟨46897252289243230538249491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62529669718990974050999321 46897252289243230538249491)
      ·
        refine ⟨70345878433864845807374237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46897252289243230538249491 70345878433864845807374237)
        ·
          refine ⟨26379704412699317177765339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70345878433864845807374237 26379704412699317177765339)
          ·
            refine ⟨39569556619048975766648009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26379704412699317177765339 39569556619048975766648009)
            ·
              refine ⟨29677167464286731824986007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39569556619048975766648009 29677167464286731824986007)
              ·
                refine ⟨44515751196430097737479011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29677167464286731824986007 44515751196430097737479011)
                ·
                  refine ⟨66773626794645146606218517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44515751196430097737479011 66773626794645146606218517)
                  ·
                    refine ⟨3130013755998991247166493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66773626794645146606218517 3130013755998991247166493)
                    ·
                      refine ⟨1173755158499621717687435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3130013755998991247166493 1173755158499621717687435)
                      ·
                        rfl

theorem cell23_2285880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_2285880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285880 prefixEnd_2285880 := by exact prefixLift 2285880
  have htrace : WordTrace (prefixWord ++ tailWord_2285880) baseStart_2285880 baseEnd_2285880 := by
    simpa [prefixWord, tailWord_2285880, baseEnd_2285880] using wordTrace_append hprefix tailTrace_2285880
  have hstable : (prefixWord ++ tailWord_2285880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285880).length < 2 ^ (prefixWord ++ tailWord_2285880).sum := by decide
  have hdescent : baseEnd_2285880 < baseStart_2285880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285900 : List Nat := [2, 2, 1, 3, 2, 1, 1, 4, 7]
def baseStart_2285900 : Nat := 118140960795 + 2285900 * 2 ^ 59
def prefixEnd_2285900 : Nat := 4983230072969 + 3 ^ 40 * 2285900 * 2
def baseEnd_2285900 : Nat := 130418380901412404381927

theorem tailTrace_2285900 : CollatzResearch.WordTrace tailWord_2285900 prefixEnd_2285900 130418380901412404381927 := by
  unfold tailWord_2285900
  simp only [CollatzResearch.WordTrace]
  refine ⟨41686811209291087741863577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55582414945721450322484769 41686811209291087741863577)
  ·
    refine ⟨31265108406968315806397683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41686811209291087741863577 31265108406968315806397683)
    ·
      refine ⟨46897662610452473709596525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31265108406968315806397683 46897662610452473709596525)
      ·
        refine ⟨17586623478919677641098697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46897662610452473709596525 17586623478919677641098697)
        ·
          refine ⟨13189967609189758230824023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17586623478919677641098697 13189967609189758230824023)
          ·
            refine ⟨19784951413784637346236035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13189967609189758230824023 19784951413784637346236035)
            ·
              refine ⟨29677427120676956019354053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19784951413784637346236035 29677427120676956019354053)
              ·
                refine ⟨5564517585126929253628885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29677427120676956019354053 5564517585126929253628885)
                ·
                  refine ⟨130418380901412404381927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5564517585126929253628885 130418380901412404381927)
                  ·
                    rfl

theorem cell23_2285900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 7].length) (baseStart_2285900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285900 prefixEnd_2285900 := by exact prefixLift 2285900
  have htrace : WordTrace (prefixWord ++ tailWord_2285900) baseStart_2285900 baseEnd_2285900 := by
    simpa [prefixWord, tailWord_2285900, baseEnd_2285900] using wordTrace_append hprefix tailTrace_2285900
  have hstable : (prefixWord ++ tailWord_2285900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285900).length < 2 ^ (prefixWord ++ tailWord_2285900).sum := by decide
  have hdescent : baseEnd_2285900 < baseStart_2285900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285937 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 2, 5, 2]
def baseStart_2285937 : Nat := 118140960795 + 2285937 * 2 ^ 59
def prefixEnd_2285937 : Nat := 4983230072969 + 3 ^ 40 * 2285937 * 2
def baseEnd_2285937 : Nat := 1173784426896927994674673

theorem tailTrace_2285937 : CollatzResearch.WordTrace tailWord_2285937 prefixEnd_2285937 1173784426896927994674673 := by
  unfold tailWord_2285937
  simp only [CollatzResearch.WordTrace]
  refine ⟨83374971919448130802824065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55583314612965420535216043 83374971919448130802824065)
  ·
    refine ⟨62531228939586098102118049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83374971919448130802824065 62531228939586098102118049)
    ·
      refine ⟨46898421704689573576588537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62531228939586098102118049 46898421704689573576588537)
      ·
        refine ⟨35173816278517180182441403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46898421704689573576588537 35173816278517180182441403)
        ·
          refine ⟨52760724417775770273662105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35173816278517180182441403 52760724417775770273662105)
          ·
            refine ⟨39570543313331827705246579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52760724417775770273662105 39570543313331827705246579)
            ·
              refine ⟨59355814969997741557869869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39570543313331827705246579 59355814969997741557869869)
              ·
                refine ⟨22258430613749153084201201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59355814969997741557869869 22258430613749153084201201)
                ·
                  refine ⟨16693822960311864813150901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22258430613749153084201201 16693822960311864813150901)
                  ·
                    refine ⟨1565045902529237326232897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16693822960311864813150901 1565045902529237326232897)
                    ·
                      refine ⟨1173784426896927994674673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1565045902529237326232897 1173784426896927994674673)
                      ·
                        rfl

theorem cell23_2285937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_2285937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285937 prefixEnd_2285937 := by exact prefixLift 2285937
  have htrace : WordTrace (prefixWord ++ tailWord_2285937) baseStart_2285937 baseEnd_2285937 := by
    simpa [prefixWord, tailWord_2285937, baseEnd_2285937] using wordTrace_append hprefix tailTrace_2285937
  have hstable : (prefixWord ++ tailWord_2285937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285937).length < 2 ^ (prefixWord ++ tailWord_2285937).sum := by decide
  have hdescent : baseEnd_2285937 < baseStart_2285937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285985 : List Nat := [1, 2, 3, 5, 2, 1, 2, 2, 5]
def baseStart_2285985 : Nat := 118140960795 + 2285985 * 2 ^ 59
def prefixEnd_2285985 : Nat := 4983230072969 + 3 ^ 40 * 2285985 * 2
def baseEnd_2285985 : Nat := 130423230440927089652717

theorem tailTrace_2285985 : CollatzResearch.WordTrace tailWord_2285985 prefixEnd_2285985 130423230440927089652717 := by
  unfold tailWord_2285985
  simp only [CollatzResearch.WordTrace]
  refine ⟨83376722623274235000571409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55584481748849490000380939 83376722623274235000571409)
  ·
    refine ⟨62532541967455676250428557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83376722623274235000571409 62532541967455676250428557)
    ·
      refine ⟨23449703237795878593910709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62532541967455676250428557 23449703237795878593910709)
      ·
        refine ⟨2198409678543363618179129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23449703237795878593910709 2198409678543363618179129)
        ·
          refine ⟨1648807258907522713634347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2198409678543363618179129 1648807258907522713634347)
          ·
            refine ⟨2473210888361284070451521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1648807258907522713634347 2473210888361284070451521)
            ·
              refine ⟨1854908166270963052838641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2473210888361284070451521 1854908166270963052838641)
              ·
                refine ⟨1391181124703222289628981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1854908166270963052838641 1391181124703222289628981)
                ·
                  refine ⟨130423230440927089652717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1391181124703222289628981 130423230440927089652717)
                  ·
                    rfl

theorem cell23_2285985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 5].length) (baseStart_2285985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2285985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2285985 prefixEnd_2285985 := by exact prefixLift 2285985
  have htrace : WordTrace (prefixWord ++ tailWord_2285985) baseStart_2285985 baseEnd_2285985 := by
    simpa [prefixWord, tailWord_2285985, baseEnd_2285985] using wordTrace_append hprefix tailTrace_2285985
  have hstable : (prefixWord ++ tailWord_2285985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285985).length < 2 ^ (prefixWord ++ tailWord_2285985).sum := by decide
  have hdescent : baseEnd_2285985 < baseStart_2285985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286007 : List Nat := [1, 1, 3, 1, 3, 3, 2, 3, 6]
def baseStart_2286007 : Nat := 118140960795 + 2286007 * 2 ^ 59
def prefixEnd_2286007 : Nat := 4983230072969 + 3 ^ 40 * 2286007 * 2
def baseEnd_2286007 : Nat := 130424485615860302311039

theorem tailTrace_2286007 : CollatzResearch.WordTrace tailWord_2286007 prefixEnd_2286007 130424485615860302311039 := by
  unfold tailWord_2286007
  simp only [CollatzResearch.WordTrace]
  refine ⟨83377525029194532757872275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55585016686129688505248183 83377525029194532757872275)
  ·
    refine ⟨125066287543791799136808413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83377525029194532757872275 125066287543791799136808413)
    ·
      refine ⟨46899857828921924676303155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125066287543791799136808413 46899857828921924676303155)
      ·
        refine ⟨70349786743382887014454733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46899857828921924676303155 70349786743382887014454733)
        ·
          refine ⟨26381170028768582630420525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70349786743382887014454733 26381170028768582630420525)
          ·
            refine ⟨9892938760788218486407697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26381170028768582630420525 9892938760788218486407697)
            ·
              refine ⟨7419704070591163864805773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9892938760788218486407697 7419704070591163864805773)
              ·
                refine ⟨2782389026471686449302165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7419704070591163864805773 2782389026471686449302165)
                ·
                  refine ⟨130424485615860302311039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2782389026471686449302165 130424485615860302311039)
                  ·
                    rfl

theorem cell23_2286007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 6].length) (baseStart_2286007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286007 prefixEnd_2286007 := by exact prefixLift 2286007
  have htrace : WordTrace (prefixWord ++ tailWord_2286007) baseStart_2286007 baseEnd_2286007 := by
    simpa [prefixWord, tailWord_2286007, baseEnd_2286007] using wordTrace_append hprefix tailTrace_2286007
  have hstable : (prefixWord ++ tailWord_2286007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286007).length < 2 ^ (prefixWord ++ tailWord_2286007).sum := by decide
  have hdescent : baseEnd_2286007 < baseStart_2286007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286028 : List Nat := [2, 2, 1, 4, 3, 1, 2, 3, 1, 4]
def baseStart_2286028 : Nat := 118140960795 + 2286028 * 2 ^ 59
def prefixEnd_2286028 : Nat := 4983230072969 + 3 ^ 40 * 2286028 * 2
def baseEnd_2286028 : Nat := 391277051212162379545585

theorem tailTrace_2286028 : CollatzResearch.WordTrace tailWord_2286028 prefixEnd_2286028 391277051212162379545585 := by
  unfold tailWord_2286028
  simp only [CollatzResearch.WordTrace]
  refine ⟨41689145481059226672193369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55585527308078968896257825 41689145481059226672193369)
  ·
    refine ⟨31266859110794420004145027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41689145481059226672193369 31266859110794420004145027)
    ·
      refine ⟨46900288666191630006217541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31266859110794420004145027 46900288666191630006217541)
      ·
        refine ⟨8793804124910930626165789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46900288666191630006217541 8793804124910930626165789)
        ·
          refine ⟨3297676546841598984812171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8793804124910930626165789 3297676546841598984812171)
          ·
            refine ⟨4946514820262398477218257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3297676546841598984812171 4946514820262398477218257)
            ·
              refine ⟨3709886115196798857913693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4946514820262398477218257 3709886115196798857913693)
              ·
                refine ⟨1391207293198799571717635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3709886115196798857913693 1391207293198799571717635)
                ·
                  refine ⟨2086810939798199357576453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391207293198799571717635 2086810939798199357576453)
                  ·
                    refine ⟨391277051212162379545585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2086810939798199357576453 391277051212162379545585)
                    ·
                      rfl

theorem cell23_2286028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 1, 4].length) (baseStart_2286028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286028 prefixEnd_2286028 := by exact prefixLift 2286028
  have htrace : WordTrace (prefixWord ++ tailWord_2286028) baseStart_2286028 baseEnd_2286028 := by
    simpa [prefixWord, tailWord_2286028, baseEnd_2286028] using wordTrace_append hprefix tailTrace_2286028
  have hstable : (prefixWord ++ tailWord_2286028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286028).length < 2 ^ (prefixWord ++ tailWord_2286028).sum := by decide
  have hdescent : baseEnd_2286028 < baseStart_2286028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286057 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 3, 1, 4]
def baseStart_2286057 : Nat := 118140960795 + 2286057 * 2 ^ 59
def prefixEnd_2286057 : Nat := 4983230072969 + 3 ^ 40 * 2286057 * 2
def baseEnd_2286057 : Nat := 1173846044575467525174121

theorem tailTrace_2286057 : CollatzResearch.WordTrace tailWord_2286057 prefixEnd_2286057 1173846044575467525174121 := by
  unfold tailWord_2286057
  simp only [CollatzResearch.WordTrace]
  refine ⟨83379348679013391297192425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55586232452675594198128283 83379348679013391297192425)
  ·
    refine ⟨62534511509260043472894319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83379348679013391297192425 62534511509260043472894319)
    ·
      refine ⟨93801767263890065209341479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62534511509260043472894319 93801767263890065209341479)
      ·
        refine ⟨140702650895835097814012219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93801767263890065209341479 140702650895835097814012219)
        ·
          refine ⟨211053976343752646721018329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140702650895835097814012219 211053976343752646721018329)
          ·
            refine ⟨158290482257814485040763747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211053976343752646721018329 158290482257814485040763747)
            ·
              refine ⟨237435723386721727561145621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158290482257814485040763747 237435723386721727561145621)
              ·
                refine ⟨11129799533752580979428701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 237435723386721727561145621 11129799533752580979428701)
                ·
                  refine ⟨4173674825157217867285763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11129799533752580979428701 4173674825157217867285763)
                  ·
                    refine ⟨6260512237735826800928645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4173674825157217867285763 6260512237735826800928645)
                    ·
                      refine ⟨1173846044575467525174121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6260512237735826800928645 1173846044575467525174121)
                      ·
                        rfl

theorem cell23_2286057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 1, 4].length) (baseStart_2286057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286057 prefixEnd_2286057 := by exact prefixLift 2286057
  have htrace : WordTrace (prefixWord ++ tailWord_2286057) baseStart_2286057 baseEnd_2286057 := by
    simpa [prefixWord, tailWord_2286057, baseEnd_2286057] using wordTrace_append hprefix tailTrace_2286057
  have hstable : (prefixWord ++ tailWord_2286057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286057).length < 2 ^ (prefixWord ++ tailWord_2286057).sum := by decide
  have hdescent : baseEnd_2286057 < baseStart_2286057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286061 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 1, 5, 2]
def baseStart_2286061 : Nat := 118140960795 + 2286061 * 2 ^ 59
def prefixEnd_2286061 : Nat := 4983230072969 + 3 ^ 40 * 2286061 * 2
def baseEnd_2286061 : Nat := 1173848098498085509524103

theorem tailTrace_2286061 : CollatzResearch.WordTrace tailWord_2286061 prefixEnd_2286061 1173848098498085509524103 := by
  unfold tailWord_2286061
  simp only [CollatzResearch.WordTrace]
  refine ⟨83379494570998899980338037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55586329713999266653558691 83379494570998899980338037)
  ·
    refine ⟨7816827616031146873156691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83379494570998899980338037 7816827616031146873156691)
    ·
      refine ⟨11725241424046720309735037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7816827616031146873156691 11725241424046720309735037)
      ·
        refine ⟨4396965534017520116150639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11725241424046720309735037 4396965534017520116150639)
        ·
          refine ⟨6595448301026280174225959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4396965534017520116150639 6595448301026280174225959)
          ·
            refine ⟨9893172451539420261338939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6595448301026280174225959 9893172451539420261338939)
            ·
              refine ⟨14839758677309130392008409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9893172451539420261338939 14839758677309130392008409)
              ·
                refine ⟨11129819007981847794006307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14839758677309130392008409 11129819007981847794006307)
                ·
                  refine ⟨16694728511972771691009461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11129819007981847794006307 16694728511972771691009461)
                  ·
                    refine ⟨1565130797997447346032137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16694728511972771691009461 1565130797997447346032137)
                    ·
                      refine ⟨1173848098498085509524103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1565130797997447346032137 1173848098498085509524103)
                      ·
                        rfl

theorem cell23_2286061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_2286061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286061 prefixEnd_2286061 := by exact prefixLift 2286061
  have htrace : WordTrace (prefixWord ++ tailWord_2286061) baseStart_2286061 baseEnd_2286061 := by
    simpa [prefixWord, tailWord_2286061, baseEnd_2286061] using wordTrace_append hprefix tailTrace_2286061
  have hstable : (prefixWord ++ tailWord_2286061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286061).length < 2 ^ (prefixWord ++ tailWord_2286061).sum := by decide
  have hdescent : baseEnd_2286061 < baseStart_2286061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286077 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_2286077 : Nat := 118140960795 + 2286077 * 2 ^ 59
def prefixEnd_2286077 : Nat := 4983230072969 + 3 ^ 40 * 2286077 * 2
def baseEnd_2286077 : Nat := 1173856314188557446924029

theorem tailTrace_2286077 : CollatzResearch.WordTrace tailWord_2286077 prefixEnd_2286077 1173856314188557446924029 := by
  unfold tailWord_2286077
  simp only [CollatzResearch.WordTrace]
  refine ⟨83380078138940934712920485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55586718759293956475280323 83380078138940934712920485)
  ·
    refine ⟨15633764651051425258672591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83380078138940934712920485 15633764651051425258672591)
    ·
      refine ⟨23450646976577137888008887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15633764651051425258672591 23450646976577137888008887)
      ·
        refine ⟨35175970464865706832013331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23450646976577137888008887 35175970464865706832013331)
        ·
          refine ⟨52763955697298560248019997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35175970464865706832013331 52763955697298560248019997)
          ·
            refine ⟨19786483386486960093007499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52763955697298560248019997 19786483386486960093007499)
            ·
              refine ⟨29679725079730440139511249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19786483386486960093007499 29679725079730440139511249)
              ·
                refine ⟨22259793809797830104633437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29679725079730440139511249 22259793809797830104633437)
                ·
                  refine ⟨8347422678674186289237539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22259793809797830104633437 8347422678674186289237539)
                  ·
                    refine ⟨12521134018011279433856309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8347422678674186289237539 12521134018011279433856309)
                    ·
                      refine ⟨1173856314188557446924029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12521134018011279433856309 1173856314188557446924029)
                      ·
                        rfl

theorem cell23_2286077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_2286077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286077 prefixEnd_2286077 := by exact prefixLift 2286077
  have htrace : WordTrace (prefixWord ++ tailWord_2286077) baseStart_2286077 baseEnd_2286077 := by
    simpa [prefixWord, tailWord_2286077, baseEnd_2286077] using wordTrace_append hprefix tailTrace_2286077
  have hstable : (prefixWord ++ tailWord_2286077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286077).length < 2 ^ (prefixWord ++ tailWord_2286077).sum := by decide
  have hdescent : baseEnd_2286077 < baseStart_2286077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286094 : List Nat := [4, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_2286094 : Nat := 118140960795 + 2286094 * 2 ^ 59
def prefixEnd_2286094 : Nat := 4983230072969 + 3 ^ 40 * 2286094 * 2
def baseEnd_2286094 : Nat := 1173865043359683880411451

theorem tailTrace_2286094 : CollatzResearch.WordTrace tailWord_2286094 prefixEnd_2286094 1173865043359683880411451 := by
  unfold tailWord_2286094
  simp only [CollatzResearch.WordTrace]
  refine ⟨10422587272484918327036167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55587132119919564410859557 10422587272484918327036167)
  ·
    refine ⟨15633880908727377490554251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10422587272484918327036167 15633880908727377490554251)
    ·
      refine ⟨23450821363091066235831377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15633880908727377490554251 23450821363091066235831377)
      ·
        refine ⟨17588116022318299676873533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23450821363091066235831377 17588116022318299676873533)
        ·
          refine ⟨6595543508369362378827575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17588116022318299676873533 6595543508369362378827575)
          ·
            refine ⟨9893315262554043568241363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6595543508369362378827575 9893315262554043568241363)
            ·
              refine ⟨14839972893831065352362045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9893315262554043568241363 14839972893831065352362045)
              ·
                refine ⟨5564989835186649507135767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14839972893831065352362045 5564989835186649507135767)
                ·
                  refine ⟨8347484752779974260703651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5564989835186649507135767 8347484752779974260703651)
                  ·
                    refine ⟨12521227129169961391055477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8347484752779974260703651 12521227129169961391055477)
                    ·
                      refine ⟨1173865043359683880411451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12521227129169961391055477 1173865043359683880411451)
                      ·
                        rfl

theorem cell23_2286094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_2286094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286094 prefixEnd_2286094 := by exact prefixLift 2286094
  have htrace : WordTrace (prefixWord ++ tailWord_2286094) baseStart_2286094 baseEnd_2286094 := by
    simpa [prefixWord, tailWord_2286094, baseEnd_2286094] using wordTrace_append hprefix tailTrace_2286094
  have hstable : (prefixWord ++ tailWord_2286094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286094).length < 2 ^ (prefixWord ++ tailWord_2286094).sum := by decide
  have hdescent : baseEnd_2286094 < baseStart_2286094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286108 : List Nat := [2, 2, 3, 1, 2, 2, 3, 1, 3, 2, 2]
def baseStart_2286108 : Nat := 118140960795 + 2286108 * 2 ^ 59
def prefixEnd_2286108 : Nat := 4983230072969 + 3 ^ 40 * 2286108 * 2
def baseEnd_2286108 : Nat := 1173872232088846825636387

theorem tailTrace_2286108 : CollatzResearch.WordTrace tailWord_2286108 prefixEnd_2286108 1173872232088846825636387 := by
  unfold tailWord_2286108
  simp only [CollatzResearch.WordTrace]
  refine ⟨41690604400914313503649489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55587472534552418004865985 41690604400914313503649489)
  ·
    refine ⟨31267953300685735127737117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41690604400914313503649489 31267953300685735127737117)
    ·
      refine ⟨11725482487757150672901419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31267953300685735127737117 11725482487757150672901419)
      ·
        refine ⟨17588223731635726009352129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11725482487757150672901419 17588223731635726009352129)
        ·
          refine ⟨13191167798726794507014097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17588223731635726009352129 13191167798726794507014097)
          ·
            refine ⟨9893375849045095880260573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13191167798726794507014097 9893375849045095880260573)
            ·
              refine ⟨3710015943391910955097715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9893375849045095880260573 3710015943391910955097715)
              ·
                refine ⟨5565023915087866432646573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3710015943391910955097715 5565023915087866432646573)
                ·
                  refine ⟨2086883968157949912242465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5565023915087866432646573 2086883968157949912242465)
                  ·
                    refine ⟨1565162976118462434181849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2086883968157949912242465 1565162976118462434181849)
                    ·
                      refine ⟨1173872232088846825636387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1565162976118462434181849 1173872232088846825636387)
                      ·
                        rfl

theorem cell23_2286108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_2286108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286108 prefixEnd_2286108 := by exact prefixLift 2286108
  have htrace : WordTrace (prefixWord ++ tailWord_2286108) baseStart_2286108 baseEnd_2286108 := by
    simpa [prefixWord, tailWord_2286108, baseEnd_2286108] using wordTrace_append hprefix tailTrace_2286108
  have hstable : (prefixWord ++ tailWord_2286108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286108).length < 2 ^ (prefixWord ++ tailWord_2286108).sum := by decide
  have hdescent : baseEnd_2286108 < baseStart_2286108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286125 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2286125 : Nat := 118140960795 + 2286125 * 2 ^ 59
def prefixEnd_2286125 : Nat := 4983230072969 + 3 ^ 40 * 2286125 * 2
def baseEnd_2286125 : Nat := 1173880961259973259123809

theorem tailTrace_2286125 : CollatzResearch.WordTrace tailWord_2286125 prefixEnd_2286125 1173880961259973259123809 := by
  unfold tailWord_2286125
  simp only [CollatzResearch.WordTrace]
  refine ⟨83381828842767038910667829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55587885895178025940445219 83381828842767038910667829)
  ·
    refine ⟨7817046454009409897875109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83381828842767038910667829 7817046454009409897875109)
    ·
      refine ⟨1465696210126764355851583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7817046454009409897875109 1465696210126764355851583)
      ·
        refine ⟨2198544315190146533777375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1465696210126764355851583 2198544315190146533777375)
        ·
          refine ⟨3297816472785219800666063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2198544315190146533777375 3297816472785219800666063)
          ·
            refine ⟨4946724709177829700999095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3297816472785219800666063 4946724709177829700999095)
            ·
              refine ⟨7420087063766744551498643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4946724709177829700999095 7420087063766744551498643)
              ·
                refine ⟨11130130595650116827247965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7420087063766744551498643 11130130595650116827247965)
                ·
                  refine ⟨4173798973368793810217987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11130130595650116827247965 4173798973368793810217987)
                  ·
                    refine ⟨6260698460053190715326981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4173798973368793810217987 6260698460053190715326981)
                    ·
                      refine ⟨1173880961259973259123809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6260698460053190715326981 1173880961259973259123809)
                      ·
                        rfl

theorem cell23_2286125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2286125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286125 prefixEnd_2286125 := by exact prefixLift 2286125
  have htrace : WordTrace (prefixWord ++ tailWord_2286125) baseStart_2286125 baseEnd_2286125 := by
    simpa [prefixWord, tailWord_2286125, baseEnd_2286125] using wordTrace_append hprefix tailTrace_2286125
  have hstable : (prefixWord ++ tailWord_2286125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286125).length < 2 ^ (prefixWord ++ tailWord_2286125).sum := by decide
  have hdescent : baseEnd_2286125 < baseStart_2286125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286141 : List Nat := [1, 4, 1, 3, 2, 2, 1, 2, 1, 3, 3]
def baseStart_2286141 : Nat := 118140960795 + 2286141 * 2 ^ 59
def prefixEnd_2286141 : Nat := 4983230072969 + 3 ^ 40 * 2286141 * 2
def baseEnd_2286141 : Nat := 1173889176950445196523735

theorem tailTrace_2286141 : CollatzResearch.WordTrace tailWord_2286141 prefixEnd_2286141 1173889176950445196523735 := by
  unfold tailWord_2286141
  simp only [CollatzResearch.WordTrace]
  refine ⟨83382412410709073643250277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55588274940472715762166851 83382412410709073643250277)
  ·
    refine ⟨15634202327007951308109427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83382412410709073643250277 15634202327007951308109427)
    ·
      refine ⟨23451303490511926962164141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15634202327007951308109427 23451303490511926962164141)
      ·
        refine ⟨8794238808941972610811553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23451303490511926962164141 8794238808941972610811553)
        ·
          refine ⟨6595679106706479458108665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8794238808941972610811553 6595679106706479458108665)
          ·
            refine ⟨4946759330029859593581499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6595679106706479458108665 4946759330029859593581499)
            ·
              refine ⟨7420138995044789390372249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4946759330029859593581499 7420138995044789390372249)
              ·
                refine ⟨5565104246283592042779187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7420138995044789390372249 5565104246283592042779187)
                ·
                  refine ⟨8347656369425388064168781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5565104246283592042779187 8347656369425388064168781)
                  ·
                    refine ⟨3130371138534520524063293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8347656369425388064168781 3130371138534520524063293)
                    ·
                      refine ⟨1173889176950445196523735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3130371138534520524063293 1173889176950445196523735)
                      ·
                        rfl

theorem cell23_2286141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_2286141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286141 prefixEnd_2286141 := by exact prefixLift 2286141
  have htrace : WordTrace (prefixWord ++ tailWord_2286141) baseStart_2286141 baseEnd_2286141 := by
    simpa [prefixWord, tailWord_2286141, baseEnd_2286141] using wordTrace_append hprefix tailTrace_2286141
  have hstable : (prefixWord ++ tailWord_2286141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286141).length < 2 ^ (prefixWord ++ tailWord_2286141).sum := by decide
  have hdescent : baseEnd_2286141 < baseStart_2286141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286147 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 4]
def baseStart_2286147 : Nat := 118140960795 + 2286147 * 2 ^ 59
def prefixEnd_2286147 : Nat := 4983230072969 + 3 ^ 40 * 2286147 * 2
def baseEnd_2286147 : Nat := 1173892257834372173048707

theorem tailTrace_2286147 : CollatzResearch.WordTrace tailWord_2286147 prefixEnd_2286147 1173892257834372173048707 := by
  unfold tailWord_2286147
  simp only [CollatzResearch.WordTrace]
  refine ⟨83382631248687336667968695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55588420832458224445312463 83382631248687336667968695)
  ·
    refine ⟨125073946873031005001953043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83382631248687336667968695 125073946873031005001953043)
    ·
      refine ⟨187610920309546507502929565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125073946873031005001953043 187610920309546507502929565)
      ·
        refine ⟨70354095116079940313598587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187610920309546507502929565 70354095116079940313598587)
        ·
          refine ⟨105531142674119910470397881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70354095116079940313598587 105531142674119910470397881)
          ·
            refine ⟨79148357005589932852798411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105531142674119910470397881 79148357005589932852798411)
            ·
              refine ⟨118722535508384899279197617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79148357005589932852798411 118722535508384899279197617)
              ·
                refine ⟨89041901631288674459398213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118722535508384899279197617 89041901631288674459398213)
                ·
                  refine ⟨16695356555866626461137165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89041901631288674459398213 16695356555866626461137165)
                  ·
                    refine ⟨6260758708449984922926437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16695356555866626461137165 6260758708449984922926437)
                    ·
                      refine ⟨1173892257834372173048707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6260758708449984922926437 1173892257834372173048707)
                      ·
                        rfl

theorem cell23_2286147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_2286147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286147 prefixEnd_2286147 := by exact prefixLift 2286147
  have htrace : WordTrace (prefixWord ++ tailWord_2286147) baseStart_2286147 baseEnd_2286147 := by
    simpa [prefixWord, tailWord_2286147, baseEnd_2286147] using wordTrace_append hprefix tailTrace_2286147
  have hstable : (prefixWord ++ tailWord_2286147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286147).length < 2 ^ (prefixWord ++ tailWord_2286147).sum := by decide
  have hdescent : baseEnd_2286147 < baseStart_2286147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286148 : List Nat := [2, 3, 5, 1, 2, 10]
def baseStart_2286148 : Nat := 118140960795 + 2286148 * 2 ^ 59
def prefixEnd_2286148 : Nat := 4983230072969 + 3 ^ 40 * 2286148 * 2
def baseEnd_2286148 : Nat := 4830834449856076827721

theorem tailTrace_2286148 : CollatzResearch.WordTrace tailWord_2286148 prefixEnd_2286148 4830834449856076827721 := by
  unfold tailWord_2286148
  simp only [CollatzResearch.WordTrace]
  refine ⟨41691333860841856919377549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55588445147789142559170065 41691333860841856919377549)
  ·
    refine ⟨15634250197815696344766581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41691333860841856919377549 15634250197815696344766581)
    ·
      refine ⟨1465710956045221532321867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15634250197815696344766581 1465710956045221532321867)
      ·
        refine ⟨2198566434067832298482801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1465710956045221532321867 2198566434067832298482801)
        ·
          refine ⟨1648924825550874223862101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2198566434067832298482801 1648924825550874223862101)
          ·
            refine ⟨4830834449856076827721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1648924825550874223862101 4830834449856076827721)
            ·
              rfl

theorem cell23_2286148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 10].length) (baseStart_2286148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286148 prefixEnd_2286148 := by exact prefixLift 2286148
  have htrace : WordTrace (prefixWord ++ tailWord_2286148) baseStart_2286148 baseEnd_2286148 := by
    simpa [prefixWord, tailWord_2286148, baseEnd_2286148] using wordTrace_append hprefix tailTrace_2286148
  have hstable : (prefixWord ++ tailWord_2286148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286148).length < 2 ^ (prefixWord ++ tailWord_2286148).sum := by decide
  have hdescent : baseEnd_2286148 < baseStart_2286148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286164 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_2286164 : Nat := 118140960795 + 2286164 * 2 ^ 59
def prefixEnd_2286164 : Nat := 4983230072969 + 3 ^ 40 * 2286164 * 2
def baseEnd_2286164 : Nat := 1173900987005498606536129

theorem tailTrace_2286164 : CollatzResearch.WordTrace tailWord_2286164 prefixEnd_2286164 1173900987005498606536129 := by
  unfold tailWord_2286164
  simp only [CollatzResearch.WordTrace]
  refine ⟨41691625644812874285668773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55588834193083832380891697 41691625644812874285668773)
  ·
    refine ⟨7817179808402413928562895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41691625644812874285668773 7817179808402413928562895)
    ·
      refine ⟨11725769712603620892844343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7817179808402413928562895 11725769712603620892844343)
      ·
        refine ⟨17588654568905431339266515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11725769712603620892844343 17588654568905431339266515)
        ·
          refine ⟨26382981853358147008899773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17588654568905431339266515 26382981853358147008899773)
          ·
            refine ⟨9893618195009305128337415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26382981853358147008899773 9893618195009305128337415)
            ·
              refine ⟨14840427292513957692506123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9893618195009305128337415 14840427292513957692506123)
              ·
                refine ⟨22260640938770936538759185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14840427292513957692506123 22260640938770936538759185)
                ·
                  refine ⟨16695480704078202404069389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22260640938770936538759185 16695480704078202404069389)
                  ·
                    refine ⟨6260805264029325901526021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16695480704078202404069389 6260805264029325901526021)
                    ·
                      refine ⟨1173900987005498606536129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6260805264029325901526021 1173900987005498606536129)
                      ·
                        rfl

theorem cell23_2286164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_2286164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286164 prefixEnd_2286164 := by exact prefixLift 2286164
  have htrace : WordTrace (prefixWord ++ tailWord_2286164) baseStart_2286164 baseEnd_2286164 := by
    simpa [prefixWord, tailWord_2286164, baseEnd_2286164] using wordTrace_append hprefix tailTrace_2286164
  have hstable : (prefixWord ++ tailWord_2286164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286164).length < 2 ^ (prefixWord ++ tailWord_2286164).sum := by decide
  have hdescent : baseEnd_2286164 < baseStart_2286164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286271 : List Nat := [1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 4]
def baseStart_2286271 : Nat := 118140960795 + 2286271 * 2 ^ 59
def prefixEnd_2286271 : Nat := 4983230072969 + 3 ^ 40 * 2286271 * 2
def baseEnd_2286271 : Nat := 1173955929435529687898137

theorem tailTrace_2286271 : CollatzResearch.WordTrace tailWord_2286271 prefixEnd_2286271 1173955929435529687898137 := by
  unfold tailWord_2286271
  simp only [CollatzResearch.WordTrace]
  refine ⟨83387153900238105845482667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55591435933492070563655111 83387153900238105845482667)
  ·
    refine ⟨125080730850357158768224001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83387153900238105845482667 125080730850357158768224001)
    ·
      refine ⟨93810548137767869076168001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125080730850357158768224001 93810548137767869076168001)
      ·
        refine ⟨70357911103325901807126001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93810548137767869076168001 70357911103325901807126001)
        ·
          refine ⟨52768433327494426355344501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70357911103325901807126001 52768433327494426355344501)
          ·
            refine ⟨4947040624452602470813547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52768433327494426355344501 4947040624452602470813547)
            ·
              refine ⟨7420560936678903706220321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4947040624452602470813547 7420560936678903706220321)
              ·
                refine ⟨5565420702509177779665241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7420560936678903706220321 5565420702509177779665241)
                ·
                  refine ⟨4174065526881883334748931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5565420702509177779665241 4174065526881883334748931)
                  ·
                    refine ⟨6261098290322825002123397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4174065526881883334748931 6261098290322825002123397)
                    ·
                      refine ⟨1173955929435529687898137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6261098290322825002123397 1173955929435529687898137)
                      ·
                        rfl

theorem cell23_2286271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_2286271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286271 prefixEnd_2286271 := by exact prefixLift 2286271
  have htrace : WordTrace (prefixWord ++ tailWord_2286271) baseStart_2286271 baseEnd_2286271 := by
    simpa [prefixWord, tailWord_2286271, baseEnd_2286271] using wordTrace_append hprefix tailTrace_2286271
  have hstable : (prefixWord ++ tailWord_2286271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286271).length < 2 ^ (prefixWord ++ tailWord_2286271).sum := by decide
  have hdescent : baseEnd_2286271 < baseStart_2286271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286308 : List Nat := [2, 3, 1, 1, 1, 5, 2, 1, 2, 2, 3]
def baseStart_2286308 : Nat := 118140960795 + 2286308 * 2 ^ 59
def prefixEnd_2286308 : Nat := 4983230072969 + 3 ^ 40 * 2286308 * 2
def baseEnd_2286308 : Nat := 1173974928219746043135467

theorem tailTrace_2286308 : CollatzResearch.WordTrace tailWord_2286308 prefixEnd_2286308 1173974928219746043135467 := by
  unfold tailWord_2286308
  simp only [CollatzResearch.WordTrace]
  refine ⟨41694251700552030582289789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55592335600736040776386385 41694251700552030582289789)
  ·
    refine ⟨15635344387707011468358671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41694251700552030582289789 15635344387707011468358671)
    ·
      refine ⟨23453016581560517202538007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15635344387707011468358671 23453016581560517202538007)
      ·
        refine ⟨35179524872340775803807011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23453016581560517202538007 35179524872340775803807011)
        ·
          refine ⟨52769287308511163705710517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35179524872340775803807011 52769287308511163705710517)
          ·
            refine ⟨4947120685172921597410361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52769287308511163705710517 4947120685172921597410361)
            ·
              refine ⟨3710340513879691198057771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4947120685172921597410361 3710340513879691198057771)
              ·
                refine ⟨5565510770819536797086657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3710340513879691198057771 5565510770819536797086657)
                ·
                  refine ⟨4174133078114652597814993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5565510770819536797086657 4174133078114652597814993)
                  ·
                    refine ⟨3130599808585989448361245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4174133078114652597814993 3130599808585989448361245)
                    ·
                      refine ⟨1173974928219746043135467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3130599808585989448361245 1173974928219746043135467)
                      ·
                        rfl

theorem cell23_2286308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_2286308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286308 prefixEnd_2286308 := by exact prefixLift 2286308
  have htrace : WordTrace (prefixWord ++ tailWord_2286308) baseStart_2286308 baseEnd_2286308 := by
    simpa [prefixWord, tailWord_2286308, baseEnd_2286308] using wordTrace_append hprefix tailTrace_2286308
  have hstable : (prefixWord ++ tailWord_2286308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286308).length < 2 ^ (prefixWord ++ tailWord_2286308).sum := by decide
  have hdescent : baseEnd_2286308 < baseStart_2286308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286314 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_2286314 : Nat := 118140960795 + 2286314 * 2 ^ 59
def prefixEnd_2286314 : Nat := 4983230072969 + 3 ^ 40 * 2286314 * 2
def baseEnd_2286314 : Nat := 1173978009103673019660439

theorem tailTrace_2286314 : CollatzResearch.WordTrace tailWord_2286314 prefixEnd_2286314 1173978009103673019660439 := by
  unfold tailWord_2286314
  simp only [CollatzResearch.WordTrace]
  refine ⟨20847180559770581047324499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55592481492721549459531997 20847180559770581047324499)
  ·
    refine ⟨31270770839655871570986749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20847180559770581047324499 31270770839655871570986749)
    ·
      refine ⟨11726539064870951839120031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31270770839655871570986749 11726539064870951839120031)
      ·
        refine ⟨17589808597306427758680047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11726539064870951839120031 17589808597306427758680047)
        ·
          refine ⟨26384712895959641638020071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17589808597306427758680047 26384712895959641638020071)
          ·
            refine ⟨39577069343939462457030107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26384712895959641638020071 39577069343939462457030107)
            ·
              refine ⟨59365604015909193685545161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39577069343939462457030107 59365604015909193685545161)
              ·
                refine ⟨44524203011931895264158871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59365604015909193685545161 44524203011931895264158871)
                ·
                  refine ⟨66786304517897842896238307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44524203011931895264158871 66786304517897842896238307)
                  ·
                    refine ⟨100179456776846764344357461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66786304517897842896238307 100179456776846764344357461)
                    ·
                      refine ⟨1173978009103673019660439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 100179456776846764344357461 1173978009103673019660439)
                      ·
                        rfl

theorem cell23_2286314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_2286314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286314 prefixEnd_2286314 := by exact prefixLift 2286314
  have htrace : WordTrace (prefixWord ++ tailWord_2286314) baseStart_2286314 baseEnd_2286314 := by
    simpa [prefixWord, tailWord_2286314, baseEnd_2286314] using wordTrace_append hprefix tailTrace_2286314
  have hstable : (prefixWord ++ tailWord_2286314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286314).length < 2 ^ (prefixWord ++ tailWord_2286314).sum := by decide
  have hdescent : baseEnd_2286314 < baseStart_2286314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286332 : List Nat := [2, 2, 2, 1, 3, 4, 2, 2, 1, 4]
def baseStart_2286332 : Nat := 118140960795 + 2286332 * 2 ^ 59
def prefixEnd_2286332 : Nat := 4983230072969 + 3 ^ 40 * 2286332 * 2
def baseEnd_2286332 : Nat := 391329083918484649745119

theorem tailTrace_2286332 : CollatzResearch.WordTrace tailWord_2286332 prefixEnd_2286332 391329083918484649745119 := by
  unfold tailWord_2286332
  simp only [CollatzResearch.WordTrace]
  refine ⟨41694689376508556631726625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55592919168678075508968833 41694689376508556631726625)
  ·
    refine ⟨31271017032381417473794969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41694689376508556631726625 31271017032381417473794969)
    ·
      refine ⟨23453262774286063105346227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31271017032381417473794969 23453262774286063105346227)
      ·
        refine ⟨35179894161429094658019341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23453262774286063105346227 35179894161429094658019341)
        ·
          refine ⟨13192460310535910496757253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35179894161429094658019341 13192460310535910496757253)
          ·
            refine ⟨2473586308225483218141985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13192460310535910496757253 2473586308225483218141985)
            ·
              refine ⟨1855189731169112413606489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2473586308225483218141985 1855189731169112413606489)
              ·
                refine ⟨1391392298376834310204867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1855189731169112413606489 1391392298376834310204867)
                ·
                  refine ⟨2087088447565251465307301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391392298376834310204867 2087088447565251465307301)
                  ·
                    refine ⟨391329083918484649745119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2087088447565251465307301 391329083918484649745119)
                    ·
                      rfl

theorem cell23_2286332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_2286332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286332 prefixEnd_2286332 := by exact prefixLift 2286332
  have htrace : WordTrace (prefixWord ++ tailWord_2286332) baseStart_2286332 baseEnd_2286332 := by
    simpa [prefixWord, tailWord_2286332, baseEnd_2286332] using wordTrace_append hprefix tailTrace_2286332
  have hstable : (prefixWord ++ tailWord_2286332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286332).length < 2 ^ (prefixWord ++ tailWord_2286332).sum := by decide
  have hdescent : baseEnd_2286332 < baseStart_2286332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286361 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 1, 8, 2]
def baseStart_2286361 : Nat := 118140960795 + 2286361 * 2 ^ 59
def prefixEnd_2286361 : Nat := 4983230072969 + 3 ^ 40 * 2286361 * 2
def baseEnd_2286361 : Nat := 1174002142694434335772723

theorem tailTrace_2286361 : CollatzResearch.WordTrace tailWord_2286361 prefixEnd_2286361 1174002142694434335772723 := by
  unfold tailWord_2286361
  simp only [CollatzResearch.WordTrace]
  refine ⟨83390436469912051216258937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55593624313274700810839291 83390436469912051216258937)
  ·
    refine ⟨62542827352434038412194203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83390436469912051216258937 62542827352434038412194203)
    ·
      refine ⟨93814241028651057618291305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62542827352434038412194203 93814241028651057618291305)
      ·
        refine ⟨70360680771488293213718479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93814241028651057618291305 70360680771488293213718479)
        ·
          refine ⟨105541021157232439820577719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70360680771488293213718479 105541021157232439820577719)
          ·
            refine ⟨158311531735848659730866579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105541021157232439820577719 158311531735848659730866579)
            ·
              refine ⟨237467297603772989596299869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158311531735848659730866579 237467297603772989596299869)
              ·
                refine ⟨89050236601414871098612451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237467297603772989596299869 89050236601414871098612451)
                ·
                  refine ⟨133575354902122306647918677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89050236601414871098612451 133575354902122306647918677)
                  ·
                    refine ⟨1565336190259245781030297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 133575354902122306647918677 1565336190259245781030297)
                    ·
                      refine ⟨1174002142694434335772723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1565336190259245781030297 1174002142694434335772723)
                      ·
                        rfl

theorem cell23_2286361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 8, 2].length) (baseStart_2286361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286361 prefixEnd_2286361 := by exact prefixLift 2286361
  have htrace : WordTrace (prefixWord ++ tailWord_2286361) baseStart_2286361 baseEnd_2286361 := by
    simpa [prefixWord, tailWord_2286361, baseEnd_2286361] using wordTrace_append hprefix tailTrace_2286361
  have hstable : (prefixWord ++ tailWord_2286361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286361).length < 2 ^ (prefixWord ++ tailWord_2286361).sum := by decide
  have hdescent : baseEnd_2286361 < baseStart_2286361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286371 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 4, 4]
def baseStart_2286371 : Nat := 118140960795 + 2286371 * 2 ^ 59
def prefixEnd_2286371 : Nat := 4983230072969 + 3 ^ 40 * 2286371 * 2
def baseEnd_2286371 : Nat := 391335759166993098882559

theorem tailTrace_2286371 : CollatzResearch.WordTrace tailWord_2286371 prefixEnd_2286371 391335759166993098882559 := by
  unfold tailWord_2286371
  simp only [CollatzResearch.WordTrace]
  refine ⟨83390801199875822924122967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55593867466583881949415311 83390801199875822924122967)
  ·
    refine ⟨125086201799813734386184451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83390801199875822924122967 125086201799813734386184451)
    ·
      refine ⟨187629302699720601579276677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125086201799813734386184451 187629302699720601579276677)
      ·
        refine ⟨35180494256197612796114377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187629302699720601579276677 35180494256197612796114377)
        ·
          refine ⟨26385370692148209597085783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35180494256197612796114377 26385370692148209597085783)
          ·
            refine ⟨39578056038222314395628675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26385370692148209597085783 39578056038222314395628675)
            ·
              refine ⟨59367084057333471593443013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39578056038222314395628675 59367084057333471593443013)
              ·
                refine ⟨11131328260750025923770565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59367084057333471593443013 11131328260750025923770565)
                ·
                  refine ⟨2087124048890629860706981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11131328260750025923770565 2087124048890629860706981)
                  ·
                    refine ⟨391335759166993098882559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2087124048890629860706981 391335759166993098882559)
                    ·
                      rfl

theorem cell23_2286371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 4].length) (baseStart_2286371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286371 prefixEnd_2286371 := by exact prefixLift 2286371
  have htrace : WordTrace (prefixWord ++ tailWord_2286371) baseStart_2286371 baseEnd_2286371 := by
    simpa [prefixWord, tailWord_2286371, baseEnd_2286371] using wordTrace_append hprefix tailTrace_2286371
  have hstable : (prefixWord ++ tailWord_2286371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286371).length < 2 ^ (prefixWord ++ tailWord_2286371).sum := by decide
  have hdescent : baseEnd_2286371 < baseStart_2286371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286445 : List Nat := [1, 5, 1, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_2286445 : Nat := 118140960795 + 2286445 * 2 ^ 59
def prefixEnd_2286445 : Nat := 4983230072969 + 3 ^ 40 * 2286445 * 2
def baseEnd_2286445 : Nat := 1174045275069412007122337

theorem tailTrace_2286445 : CollatzResearch.WordTrace tailWord_2286445 prefixEnd_2286445 1174045275069412007122337 := by
  unfold tailWord_2286445
  simp only [CollatzResearch.WordTrace]
  refine ⟨83393500201607733562316789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55595666801071822374877859 83393500201607733562316789)
  ·
    refine ⟨7818140643900725021467199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83393500201607733562316789 7818140643900725021467199)
    ·
      refine ⟨11727210965851087532200799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7818140643900725021467199 11727210965851087532200799)
      ·
        refine ⟨17590816448776631298301199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11727210965851087532200799 17590816448776631298301199)
        ·
          refine ⟨26386224673164946947451799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17590816448776631298301199 26386224673164946947451799)
          ·
            refine ⟨39579337009747420421177699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26386224673164946947451799 39579337009747420421177699)
            ·
              refine ⟨59369005514621130631766549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39579337009747420421177699 59369005514621130631766549)
              ·
                refine ⟨2782922133497865498364057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59369005514621130631766549 2782922133497865498364057)
                ·
                  refine ⟨2087191600123399123773043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2782922133497865498364057 2087191600123399123773043)
                  ·
                    refine ⟨3130787400185098685659565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2087191600123399123773043 3130787400185098685659565)
                    ·
                      refine ⟨1174045275069412007122337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3130787400185098685659565 1174045275069412007122337)
                      ·
                        rfl

theorem cell23_2286445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_2286445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286445 prefixEnd_2286445 := by exact prefixLift 2286445
  have htrace : WordTrace (prefixWord ++ tailWord_2286445) baseStart_2286445 baseEnd_2286445 := by
    simpa [prefixWord, tailWord_2286445, baseEnd_2286445] using wordTrace_append hprefix tailTrace_2286445
  have hstable : (prefixWord ++ tailWord_2286445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286445).length < 2 ^ (prefixWord ++ tailWord_2286445).sum := by decide
  have hdescent : baseEnd_2286445 < baseStart_2286445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286446 : List Nat := [4, 1, 2, 3, 3, 1, 1, 1, 3, 2, 2]
def baseStart_2286446 : Nat := 118140960795 + 2286446 * 2 ^ 59
def prefixEnd_2286446 : Nat := 4983230072969 + 3 ^ 40 * 2286446 * 2
def baseEnd_2286446 : Nat := 1174045788550066503209833

theorem tailTrace_2286446 : CollatzResearch.WordTrace tailWord_2286446 prefixEnd_2286446 1174045788550066503209833 := by
  unfold tailWord_2286446
  simp only [CollatzResearch.WordTrace]
  refine ⟨10424192084325513841637899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55595691116402740488735461 10424192084325513841637899)
  ·
    refine ⟨15636288126488270762456849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10424192084325513841637899 15636288126488270762456849)
    ·
      refine ⟨11727216094866203071842637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15636288126488270762456849 11727216094866203071842637)
      ·
        refine ⟨4397706035574826151940989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11727216094866203071842637 4397706035574826151940989)
        ·
          refine ⟨1649139763340559806977871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4397706035574826151940989 1649139763340559806977871)
          ·
            refine ⟨2473709645010839710466807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1649139763340559806977871 2473709645010839710466807)
            ·
              refine ⟨3710564467516259565700211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2473709645010839710466807 3710564467516259565700211)
              ·
                refine ⟨5565846701274389348550317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3710564467516259565700211 5565846701274389348550317)
                ·
                  refine ⟨2087192512977896005706369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5565846701274389348550317 2087192512977896005706369)
                  ·
                    refine ⟨1565394384733422004279777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2087192512977896005706369 1565394384733422004279777)
                    ·
                      refine ⟨1174045788550066503209833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1565394384733422004279777 1174045788550066503209833)
                      ·
                        rfl

theorem cell23_2286446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_2286446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286446 prefixEnd_2286446 := by exact prefixLift 2286446
  have htrace : WordTrace (prefixWord ++ tailWord_2286446) baseStart_2286446 baseEnd_2286446 := by
    simpa [prefixWord, tailWord_2286446, baseEnd_2286446] using wordTrace_append hprefix tailTrace_2286446
  have hstable : (prefixWord ++ tailWord_2286446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286446).length < 2 ^ (prefixWord ++ tailWord_2286446).sum := by decide
  have hdescent : baseEnd_2286446 < baseStart_2286446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286461 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 2, 6]
def baseStart_2286461 : Nat := 118140960795 + 2286461 * 2 ^ 59
def prefixEnd_2286461 : Nat := 4983230072969 + 3 ^ 40 * 2286461 * 2
def baseEnd_2286461 : Nat := 391351163586627981507421

theorem tailTrace_2286461 : CollatzResearch.WordTrace tailWord_2286461 prefixEnd_2286461 391351163586627981507421 := by
  unfold tailWord_2286461
  simp only [CollatzResearch.WordTrace]
  refine ⟨83394083769549768294899237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55596055846366512196599491 83394083769549768294899237)
  ·
    refine ⟨15636390706790581555293607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83394083769549768294899237 15636390706790581555293607)
    ·
      refine ⟨23454586060185872332940411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15636390706790581555293607 23454586060185872332940411)
      ·
        refine ⟨35181879090278808499410617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23454586060185872332940411 35181879090278808499410617)
        ·
          refine ⟨26386409317709106374557963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35181879090278808499410617 26386409317709106374557963)
          ·
            refine ⟨39579613976563659561836945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26386409317709106374557963 39579613976563659561836945)
            ·
              refine ⟨29684710482422744671377709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39579613976563659561836945 29684710482422744671377709)
              ·
                refine ⟨11131766430908529251766641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29684710482422744671377709 11131766430908529251766641)
                ·
                  refine ⟨8348824823181396938824981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11131766430908529251766641 8348824823181396938824981)
                  ·
                    refine ⟨391351163586627981507421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8348824823181396938824981 391351163586627981507421)
                    ·
                      rfl

theorem cell23_2286461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_2286461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286461 prefixEnd_2286461 := by exact prefixLift 2286461
  have htrace : WordTrace (prefixWord ++ tailWord_2286461) baseStart_2286461 baseEnd_2286461 := by
    simpa [prefixWord, tailWord_2286461, baseEnd_2286461] using wordTrace_append hprefix tailTrace_2286461
  have hstable : (prefixWord ++ tailWord_2286461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286461).length < 2 ^ (prefixWord ++ tailWord_2286461).sum := by decide
  have hdescent : baseEnd_2286461 < baseStart_2286461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286466 : List Nat := [3, 4, 2, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_2286466 : Nat := 118140960795 + 2286466 * 2 ^ 59
def prefixEnd_2286466 : Nat := 4983230072969 + 3 ^ 40 * 2286466 * 2
def baseEnd_2286466 : Nat := 1174056058163156424959741

theorem tailTrace_2286466 : CollatzResearch.WordTrace tailWord_2286466 prefixEnd_2286466 1174056058163156424959741 := by
  unfold tailWord_2286466
  simp only [CollatzResearch.WordTrace]
  refine ⟨20848566533632913537207813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55596177423021102765887501 20848566533632913537207813)
  ·
    refine ⟨3909106225056171288226465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20848566533632913537207813 3909106225056171288226465)
    ·
      refine ⟨2931829668792128466169849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3909106225056171288226465 2931829668792128466169849)
      ·
        refine ⟨2198872251594096349627387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2931829668792128466169849 2198872251594096349627387)
        ·
          refine ⟨3298308377391144524441081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2198872251594096349627387 3298308377391144524441081)
          ·
            refine ⟨2473731283043358393330811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3298308377391144524441081 2473731283043358393330811)
            ·
              refine ⟨3710596924565037589996217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2473731283043358393330811 3710596924565037589996217)
              ·
                refine ⟨2782947693423778192497163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3710596924565037589996217 2782947693423778192497163)
                ·
                  refine ⟨4174421540135667288745745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2782947693423778192497163 4174421540135667288745745)
                  ·
                    refine ⟨3130816155101750466559309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4174421540135667288745745 3130816155101750466559309)
                    ·
                      refine ⟨1174056058163156424959741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3130816155101750466559309 1174056058163156424959741)
                      ·
                        rfl

theorem cell23_2286466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_2286466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286466 prefixEnd_2286466 := by exact prefixLift 2286466
  have htrace : WordTrace (prefixWord ++ tailWord_2286466) baseStart_2286466 baseEnd_2286466 := by
    simpa [prefixWord, tailWord_2286466, baseEnd_2286466] using wordTrace_append hprefix tailTrace_2286466
  have hstable : (prefixWord ++ tailWord_2286466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286466).length < 2 ^ (prefixWord ++ tailWord_2286466).sum := by decide
  have hdescent : baseEnd_2286466 < baseStart_2286466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286472 : List Nat := [2, 1, 3, 3, 2, 1, 3, 2, 1, 3, 2]
def baseStart_2286472 : Nat := 118140960795 + 2286472 * 2 ^ 59
def prefixEnd_2286472 : Nat := 4983230072969 + 3 ^ 40 * 2286472 * 2
def baseEnd_2286472 : Nat := 1174059139047083401484713

theorem tailTrace_2286472 : CollatzResearch.WordTrace tailWord_2286472 prefixEnd_2286472 1174059139047083401484713 := by
  unfold tailWord_2286472
  simp only [CollatzResearch.WordTrace]
  refine ⟨41697242486254958586774835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55596323315006611449033113 41697242486254958586774835)
  ·
    refine ⟨62545863729382437880162253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41697242486254958586774835 62545863729382437880162253)
    ·
      refine ⟨23454698898518414205060845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62545863729382437880162253 23454698898518414205060845)
      ·
        refine ⟨8795512086944405326897817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23454698898518414205060845 8795512086944405326897817)
        ·
          refine ⟨6596634065208303995173363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8795512086944405326897817 6596634065208303995173363)
          ·
            refine ⟨9894951097812455992760045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6596634065208303995173363 9894951097812455992760045)
            ·
              refine ⟨3710606661679670997285017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9894951097812455992760045 3710606661679670997285017)
              ·
                refine ⟨2782954996259753247963763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3710606661679670997285017 2782954996259753247963763)
                ·
                  refine ⟨4174432494389629871945645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2782954996259753247963763 4174432494389629871945645)
                  ·
                    refine ⟨1565412185396111201979617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4174432494389629871945645 1565412185396111201979617)
                    ·
                      refine ⟨1174059139047083401484713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1565412185396111201979617 1174059139047083401484713)
                      ·
                        rfl

theorem cell23_2286472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_2286472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286472 prefixEnd_2286472 := by exact prefixLift 2286472
  have htrace : WordTrace (prefixWord ++ tailWord_2286472) baseStart_2286472 baseEnd_2286472 := by
    simpa [prefixWord, tailWord_2286472, baseEnd_2286472] using wordTrace_append hprefix tailTrace_2286472
  have hstable : (prefixWord ++ tailWord_2286472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286472).length < 2 ^ (prefixWord ++ tailWord_2286472).sum := by decide
  have hdescent : baseEnd_2286472 < baseStart_2286472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286481 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 4]
def baseStart_2286481 : Nat := 118140960795 + 2286481 * 2 ^ 59
def prefixEnd_2286481 : Nat := 4983230072969 + 3 ^ 40 * 2286481 * 2
def baseEnd_2286481 : Nat := 1174063760372973866272171

theorem tailTrace_2286481 : CollatzResearch.WordTrace tailWord_2286481 prefixEnd_2286481 1174063760372973866272171 := by
  unfold tailWord_2286481
  simp only [CollatzResearch.WordTrace]
  refine ⟨83394813229477311710627297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55596542152984874473751531 83394813229477311710627297)
  ·
    refine ⟨62546109922107983782970473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83394813229477311710627297 62546109922107983782970473)
    ·
      refine ⟨46909582441580987837227855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62546109922107983782970473 46909582441580987837227855)
      ·
        refine ⟨70364373662371481755841783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46909582441580987837227855 70364373662371481755841783)
        ·
          refine ⟨105546560493557222633762675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70364373662371481755841783 105546560493557222633762675)
          ·
            refine ⟨158319840740335833950644013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105546560493557222633762675 158319840740335833950644013)
            ·
              refine ⟨59369940277625937731491505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158319840740335833950644013 59369940277625937731491505)
              ·
                refine ⟨44527455208219453298618629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59369940277625937731491505 44527455208219453298618629)
                ·
                  refine ⟨8348897851541147493490993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44527455208219453298618629 8348897851541147493490993)
                  ·
                    refine ⟨6261673388655860620118245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8348897851541147493490993 6261673388655860620118245)
                    ·
                      refine ⟨1174063760372973866272171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6261673388655860620118245 1174063760372973866272171)
                      ·
                        rfl

theorem cell23_2286481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_2286481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286481 prefixEnd_2286481 := by exact prefixLift 2286481
  have htrace : WordTrace (prefixWord ++ tailWord_2286481) baseStart_2286481 baseEnd_2286481 := by
    simpa [prefixWord, tailWord_2286481, baseEnd_2286481] using wordTrace_append hprefix tailTrace_2286481
  have hstable : (prefixWord ++ tailWord_2286481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286481).length < 2 ^ (prefixWord ++ tailWord_2286481).sum := by decide
  have hdescent : baseEnd_2286481 < baseStart_2286481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286485 : List Nat := [1, 3, 2, 1, 1, 5, 1, 2, 1, 4, 2]
def baseStart_2286485 : Nat := 118140960795 + 2286485 * 2 ^ 59
def prefixEnd_2286485 : Nat := 4983230072969 + 3 ^ 40 * 2286485 * 2
def baseEnd_2286485 : Nat := 1174065814295591850622153

theorem tailTrace_2286485 : CollatzResearch.WordTrace tailWord_2286485 prefixEnd_2286485 1174065814295591850622153 := by
  unfold tailWord_2286485
  simp only [CollatzResearch.WordTrace]
  refine ⟨83394959121462820393772909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55596639414308546929181939 83394959121462820393772909)
  ·
    refine ⟨31273109670548557647664841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83394959121462820393772909 31273109670548557647664841)
    ·
      refine ⟨23454832252911418235748631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31273109670548557647664841 23454832252911418235748631)
      ·
        refine ⟨35182248379367127353622947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23454832252911418235748631 35182248379367127353622947)
        ·
          refine ⟨52773372569050691030434421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35182248379367127353622947 52773372569050691030434421)
          ·
            refine ⟨4947503678348502284103227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52773372569050691030434421 4947503678348502284103227)
            ·
              refine ⟨7421255517522753426154841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4947503678348502284103227 7421255517522753426154841)
              ·
                refine ⟨5565941638142065069616131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7421255517522753426154841 5565941638142065069616131)
                ·
                  refine ⟨8348912457213097604424197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5565941638142065069616131 8348912457213097604424197)
                  ·
                    refine ⟨1565421085727455800829537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8348912457213097604424197 1565421085727455800829537)
                    ·
                      refine ⟨1174065814295591850622153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1565421085727455800829537 1174065814295591850622153)
                      ·
                        rfl

theorem cell23_2286485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_2286485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286485 prefixEnd_2286485 := by exact prefixLift 2286485
  have htrace : WordTrace (prefixWord ++ tailWord_2286485) baseStart_2286485 baseEnd_2286485 := by
    simpa [prefixWord, tailWord_2286485, baseEnd_2286485] using wordTrace_append hprefix tailTrace_2286485
  have hstable : (prefixWord ++ tailWord_2286485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286485).length < 2 ^ (prefixWord ++ tailWord_2286485).sum := by decide
  have hdescent : baseEnd_2286485 < baseStart_2286485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286508 : List Nat := [2, 2, 1, 1, 1, 1, 2, 8, 5]
def baseStart_2286508 : Nat := 118140960795 + 2286508 * 2 ^ 59
def prefixEnd_2286508 : Nat := 4983230072969 + 3 ^ 40 * 2286508 * 2
def baseEnd_2286508 : Nat := 130453069372293917848283

theorem tailTrace_2286508 : CollatzResearch.WordTrace tailWord_2286508 prefixEnd_2286508 130453069372293917848283 := by
  unfold tailWord_2286508
  simp only [CollatzResearch.WordTrace]
  refine ⟨41697899000189747660930089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55597198666919663547906785 41697899000189747660930089)
  ·
    refine ⟨31273424250142310745697567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41697899000189747660930089 31273424250142310745697567)
    ·
      refine ⟨46910136375213466118546351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31273424250142310745697567 46910136375213466118546351)
      ·
        refine ⟨70365204562820199177819527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46910136375213466118546351 70365204562820199177819527)
        ·
          refine ⟨105547806844230298766729291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70365204562820199177819527 105547806844230298766729291)
          ·
            refine ⟨158321710266345448150093937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105547806844230298766729291 158321710266345448150093937)
            ·
              refine ⟨118741282699759086112570453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158321710266345448150093937 118741282699759086112570453)
              ·
                refine ⟨1391499406637801790381685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 118741282699759086112570453 1391499406637801790381685)
                ·
                  refine ⟨130453069372293917848283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1391499406637801790381685 130453069372293917848283)
                  ·
                    rfl

theorem cell23_2286508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 5].length) (baseStart_2286508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286508 prefixEnd_2286508 := by exact prefixLift 2286508
  have htrace : WordTrace (prefixWord ++ tailWord_2286508) baseStart_2286508 baseEnd_2286508 := by
    simpa [prefixWord, tailWord_2286508, baseEnd_2286508] using wordTrace_append hprefix tailTrace_2286508
  have hstable : (prefixWord ++ tailWord_2286508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286508).length < 2 ^ (prefixWord ++ tailWord_2286508).sum := by decide
  have hdescent : baseEnd_2286508 < baseStart_2286508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286575 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 2, 4, 2]
def baseStart_2286575 : Nat := 118140960795 + 2286575 * 2 ^ 59
def prefixEnd_2286575 : Nat := 4983230072969 + 3 ^ 40 * 2286575 * 2
def baseEnd_2286575 : Nat := 1174112027554496498496739

theorem tailTrace_2286575 : CollatzResearch.WordTrace tailWord_2286575 prefixEnd_2286575 1174112027554496498496739 := by
  unfold tailWord_2286575
  simp only [CollatzResearch.WordTrace]
  refine ⟨83398241691136765764549179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55598827794091177176366119 83398241691136765764549179)
  ·
    refine ⟨125097362536705148646823769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83398241691136765764549179 125097362536705148646823769)
    ·
      refine ⟨93823021902528861485117827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125097362536705148646823769 93823021902528861485117827)
      ·
        refine ⟨140734532853793292227676741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93823021902528861485117827 140734532853793292227676741)
        ·
          refine ⟨26387724910086242292689389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140734532853793292227676741 26387724910086242292689389)
          ·
            refine ⟨9895396841282340859758521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26387724910086242292689389 9895396841282340859758521)
            ·
              refine ⟨7421547630961755644818891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9895396841282340859758521 7421547630961755644818891)
              ·
                refine ⟨11132321446442633467228337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7421547630961755644818891 11132321446442633467228337)
                ·
                  refine ⟨8349241084831975100421253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11132321446442633467228337 8349241084831975100421253)
                  ·
                    refine ⟨1565482703405995331328985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8349241084831975100421253 1565482703405995331328985)
                    ·
                      refine ⟨1174112027554496498496739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1565482703405995331328985 1174112027554496498496739)
                      ·
                        rfl

theorem cell23_2286575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 4, 2].length) (baseStart_2286575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286575 prefixEnd_2286575 := by exact prefixLift 2286575
  have htrace : WordTrace (prefixWord ++ tailWord_2286575) baseStart_2286575 baseEnd_2286575 := by
    simpa [prefixWord, tailWord_2286575, baseEnd_2286575] using wordTrace_append hprefix tailTrace_2286575
  have hstable : (prefixWord ++ tailWord_2286575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286575).length < 2 ^ (prefixWord ++ tailWord_2286575).sum := by decide
  have hdescent : baseEnd_2286575 < baseStart_2286575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286591 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 9]
def baseStart_2286591 : Nat := 118140960795 + 2286591 * 2 ^ 59
def prefixEnd_2286591 : Nat := 4983230072969 + 3 ^ 40 * 2286591 * 2
def baseEnd_2286591 : Nat := 1174120243244968435896665

theorem tailTrace_2286591 : CollatzResearch.WordTrace tailWord_2286591 prefixEnd_2286591 1174120243244968435896665 := by
  unfold tailWord_2286591
  simp only [CollatzResearch.WordTrace]
  refine ⟨83398825259078800497131627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55599216839385866998087751 83398825259078800497131627)
  ·
    refine ⟨125098237888618200745697441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83398825259078800497131627 125098237888618200745697441)
    ·
      refine ⟨93823678416463650559273081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125098237888618200745697441 93823678416463650559273081)
      ·
        refine ⟨70367758812347737919454811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93823678416463650559273081 70367758812347737919454811)
        ·
          refine ⟨105551638218521606879182217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70367758812347737919454811 105551638218521606879182217)
          ·
            refine ⟨79163728663891205159386663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105551638218521606879182217 79163728663891205159386663)
            ·
              refine ⟨118745592995836807739079995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79163728663891205159386663 118745592995836807739079995)
              ·
                refine ⟨178118389493755211608619993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118745592995836807739079995 178118389493755211608619993)
                ·
                  refine ⟨133588792120316408706464995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178118389493755211608619993 133588792120316408706464995)
                  ·
                    refine ⟨200383188180474613059697493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 133588792120316408706464995 200383188180474613059697493)
                    ·
                      refine ⟨1174120243244968435896665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 200383188180474613059697493 1174120243244968435896665)
                      ·
                        rfl

theorem cell23_2286591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_2286591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286591 prefixEnd_2286591 := by exact prefixLift 2286591
  have htrace : WordTrace (prefixWord ++ tailWord_2286591) baseStart_2286591 baseEnd_2286591 := by
    simpa [prefixWord, tailWord_2286591, baseEnd_2286591] using wordTrace_append hprefix tailTrace_2286591
  have hstable : (prefixWord ++ tailWord_2286591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286591).length < 2 ^ (prefixWord ++ tailWord_2286591).sum := by decide
  have hdescent : baseEnd_2286591 < baseStart_2286591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286635 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 4, 3, 2]
def baseStart_2286635 : Nat := 118140960795 + 2286635 * 2 ^ 59
def prefixEnd_2286635 : Nat := 4983230072969 + 3 ^ 40 * 2286635 * 2
def baseEnd_2286635 : Nat := 1174142836393766263746463

theorem tailTrace_2286635 : CollatzResearch.WordTrace tailWord_2286635 prefixEnd_2286635 1174142836393766263746463 := by
  unfold tailWord_2286635
  simp only [CollatzResearch.WordTrace]
  refine ⟨83400430070919396011733359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55600286713946264007822239 83400430070919396011733359)
  ·
    refine ⟨125100645106379094017600039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83400430070919396011733359 125100645106379094017600039)
    ·
      refine ⟨187650967659568641026400059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125100645106379094017600039 187650967659568641026400059)
      ·
        refine ⟨281476451489352961539600089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187650967659568641026400059 281476451489352961539600089)
        ·
          refine ⟨211107338617014721154700067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281476451489352961539600089 211107338617014721154700067)
          ·
            refine ⟨316661007925522081732050101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211107338617014721154700067 316661007925522081732050101)
            ·
              refine ⟨29686969493017695162379697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 316661007925522081732050101 29686969493017695162379697)
              ·
                refine ⟨22265227119763271371784773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29686969493017695162379697 22265227119763271371784773)
                ·
                  refine ⟨4174730084955613382209645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22265227119763271371784773 4174730084955613382209645)
                  ·
                    refine ⟨1565523781858355018328617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4174730084955613382209645 1565523781858355018328617)
                    ·
                      refine ⟨1174142836393766263746463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1565523781858355018328617 1174142836393766263746463)
                      ·
                        rfl

theorem cell23_2286635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 3, 2].length) (baseStart_2286635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286635 prefixEnd_2286635 := by exact prefixLift 2286635
  have htrace : WordTrace (prefixWord ++ tailWord_2286635) baseStart_2286635 baseEnd_2286635 := by
    simpa [prefixWord, tailWord_2286635, baseEnd_2286635] using wordTrace_append hprefix tailTrace_2286635
  have hstable : (prefixWord ++ tailWord_2286635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286635).length < 2 ^ (prefixWord ++ tailWord_2286635).sum := by decide
  have hdescent : baseEnd_2286635 < baseStart_2286635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286652 : List Nat := [2, 2, 2, 2, 2, 2, 1, 3, 2, 3, 2]
def baseStart_2286652 : Nat := 118140960795 + 2286652 * 2 ^ 59
def prefixEnd_2286652 : Nat := 4983230072969 + 3 ^ 40 * 2286652 * 2
def baseEnd_2286652 : Nat := 1174151565564892697233885

theorem tailTrace_2286652 : CollatzResearch.WordTrace tailWord_2286652 prefixEnd_2286652 1174151565564892697233885 := by
  unfold tailWord_2286652
  simp only [CollatzResearch.WordTrace]
  refine ⟨41700525055928903957551105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55600700074571871943401473 41700525055928903957551105)
  ·
    refine ⟨31275393791946677968163329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41700525055928903957551105 31275393791946677968163329)
    ·
      refine ⟨23456545343960008476122497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31275393791946677968163329 23456545343960008476122497)
      ·
        refine ⟨17592409007970006357091873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23456545343960008476122497 17592409007970006357091873)
        ·
          refine ⟨13194306755977504767818905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17592409007970006357091873 13194306755977504767818905)
          ·
            refine ⟨9895730066983128575864179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13194306755977504767818905 9895730066983128575864179)
            ·
              refine ⟨14843595100474692863796269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9895730066983128575864179 14843595100474692863796269)
              ·
                refine ⟨5566348162678009823923601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14843595100474692863796269 5566348162678009823923601)
                ·
                  refine ⟨4174761122008507367942701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5566348162678009823923601 4174761122008507367942701)
                  ·
                    refine ⟨1565535420753190262978513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4174761122008507367942701 1565535420753190262978513)
                    ·
                      refine ⟨1174151565564892697233885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1565535420753190262978513 1174151565564892697233885)
                      ·
                        rfl

theorem cell23_2286652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_2286652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286652 prefixEnd_2286652 := by exact prefixLift 2286652
  have htrace : WordTrace (prefixWord ++ tailWord_2286652) baseStart_2286652 baseEnd_2286652 := by
    simpa [prefixWord, tailWord_2286652, baseEnd_2286652] using wordTrace_append hprefix tailTrace_2286652
  have hstable : (prefixWord ++ tailWord_2286652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286652).length < 2 ^ (prefixWord ++ tailWord_2286652).sum := by decide
  have hdescent : baseEnd_2286652 < baseStart_2286652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286669 : List Nat := [1, 6, 1, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_2286669 : Nat := 118140960795 + 2286669 * 2 ^ 59
def prefixEnd_2286669 : Nat := 4983230072969 + 3 ^ 40 * 2286669 * 2
def baseEnd_2286669 : Nat := 1174160294736019130721307

theorem tailTrace_2286669 : CollatzResearch.WordTrace tailWord_2286669 prefixEnd_2286669 1174160294736019130721307 := by
  unfold tailWord_2286669
  simp only [CollatzResearch.WordTrace]
  refine ⟨83401670152796219818471061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55601113435197479878980707 83401670152796219818471061)
  ·
    refine ⟨3909453288412322803990831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 83401670152796219818471061 3909453288412322803990831)
    ·
      refine ⟨5864179932618484205986247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3909453288412322803990831 5864179932618484205986247)
      ·
        refine ⟨8796269898927726308979371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5864179932618484205986247 8796269898927726308979371)
        ·
          refine ⟨13194404848391589463469057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8796269898927726308979371 13194404848391589463469057)
          ·
            refine ⟨9895803636293692097601793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13194404848391589463469057 9895803636293692097601793)
            ·
              refine ⟨7421852727220269073201345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9895803636293692097601793 7421852727220269073201345)
              ·
                refine ⟨5566389545415201804901009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7421852727220269073201345 5566389545415201804901009)
                ·
                  refine ⟨4174792159061401353675757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5566389545415201804901009 4174792159061401353675757)
                  ·
                    refine ⟨1565547059648025507628409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4174792159061401353675757 1565547059648025507628409)
                    ·
                      refine ⟨1174160294736019130721307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1565547059648025507628409 1174160294736019130721307)
                      ·
                        rfl

theorem cell23_2286669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_2286669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286669 prefixEnd_2286669 := by exact prefixLift 2286669
  have htrace : WordTrace (prefixWord ++ tailWord_2286669) baseStart_2286669 baseEnd_2286669 := by
    simpa [prefixWord, tailWord_2286669, baseEnd_2286669] using wordTrace_append hprefix tailTrace_2286669
  have hstable : (prefixWord ++ tailWord_2286669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286669).length < 2 ^ (prefixWord ++ tailWord_2286669).sum := by decide
  have hdescent : baseEnd_2286669 < baseStart_2286669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286675 : List Nat := [1, 1, 1, 2, 1, 1, 2, 8, 2, 4]
def baseStart_2286675 : Nat := 118140960795 + 2286675 * 2 ^ 59
def prefixEnd_2286675 : Nat := 4983230072969 + 3 ^ 40 * 2286675 * 2
def baseEnd_2286675 : Nat := 391387791873315369082093

theorem tailTrace_2286675 : CollatzResearch.WordTrace tailWord_2286675 prefixEnd_2286675 391387791873315369082093 := by
  unfold tailWord_2286675
  simp only [CollatzResearch.WordTrace]
  refine ⟨83401888990774482843189479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55601259327182988562126319 83401888990774482843189479)
  ·
    refine ⟨125102833486161724264784219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83401888990774482843189479 125102833486161724264784219)
    ·
      refine ⟨187654250229242586397176329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125102833486161724264784219 187654250229242586397176329)
      ·
        refine ⟨140740687671931939797882247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187654250229242586397176329 140740687671931939797882247)
        ·
          refine ⟨211111031507897909696823371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140740687671931939797882247 211111031507897909696823371)
          ·
            refine ⟨316666547261846864545235057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211111031507897909696823371 316666547261846864545235057)
            ·
              refine ⟨237499910446385148408926293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316666547261846864545235057 237499910446385148408926293)
              ·
                refine ⟨2783202075543575957917105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 237499910446385148408926293 2783202075543575957917105)
                ·
                  refine ⟨2087401556657681968437829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2783202075543575957917105 2087401556657681968437829)
                  ·
                    refine ⟨391387791873315369082093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2087401556657681968437829 391387791873315369082093)
                    ·
                      rfl

theorem cell23_2286675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 4].length) (baseStart_2286675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286675 prefixEnd_2286675 := by exact prefixLift 2286675
  have htrace : WordTrace (prefixWord ++ tailWord_2286675) baseStart_2286675 baseEnd_2286675 := by
    simpa [prefixWord, tailWord_2286675, baseEnd_2286675] using wordTrace_append hprefix tailTrace_2286675
  have hstable : (prefixWord ++ tailWord_2286675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286675).length < 2 ^ (prefixWord ++ tailWord_2286675).sum := by decide
  have hdescent : baseEnd_2286675 < baseStart_2286675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286676 : List Nat := [2, 4, 1, 1, 1, 1, 6, 2, 1, 1, 3]
def baseStart_2286676 : Nat := 118140960795 + 2286676 * 2 ^ 59
def prefixEnd_2286676 : Nat := 4983230072969 + 3 ^ 40 * 2286676 * 2
def baseEnd_2286676 : Nat := 1174163889100600603333775

theorem tailTrace_2286676 : CollatzResearch.WordTrace tailWord_2286676 prefixEnd_2286676 1174163889100600603333775 := by
  unfold tailWord_2286676
  simp only [CollatzResearch.WordTrace]
  refine ⟨41700962731885430006987941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55601283642513906675983921 41700962731885430006987941)
  ·
    refine ⟨7818930512228518126310239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41700962731885430006987941 7818930512228518126310239)
    ·
      refine ⟨11728395768342777189465359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7818930512228518126310239 11728395768342777189465359)
      ·
        refine ⟨17592593652514165784198039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11728395768342777189465359 17592593652514165784198039)
        ·
          refine ⟨26388890478771248676297059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17592593652514165784198039 26388890478771248676297059)
          ·
            refine ⟨39583335718156873014445589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26388890478771248676297059 39583335718156873014445589)
            ·
              refine ⟨1855468861788603422552137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39583335718156873014445589 1855468861788603422552137)
              ·
                refine ⟨1391601646341452566914103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1855468861788603422552137 1391601646341452566914103)
                ·
                  refine ⟨2087402469512178850371155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391601646341452566914103 2087402469512178850371155)
                  ·
                    refine ⟨3131103704268268275556733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2087402469512178850371155 3131103704268268275556733)
                    ·
                      refine ⟨1174163889100600603333775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3131103704268268275556733 1174163889100600603333775)
                      ·
                        rfl

theorem cell23_2286676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_2286676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286676 prefixEnd_2286676 := by exact prefixLift 2286676
  have htrace : WordTrace (prefixWord ++ tailWord_2286676) baseStart_2286676 baseEnd_2286676 := by
    simpa [prefixWord, tailWord_2286676, baseEnd_2286676] using wordTrace_append hprefix tailTrace_2286676
  have hstable : (prefixWord ++ tailWord_2286676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286676).length < 2 ^ (prefixWord ++ tailWord_2286676).sum := by decide
  have hdescent : baseEnd_2286676 < baseStart_2286676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286695 : List Nat := [1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_2286695 : Nat := 118140960795 + 2286695 * 2 ^ 59
def prefixEnd_2286695 : Nat := 4983230072969 + 3 ^ 40 * 2286695 * 2
def baseEnd_2286695 : Nat := 1174173645233036028996187

theorem tailTrace_2286695 : CollatzResearch.WordTrace tailWord_2286695 prefixEnd_2286695 1174173645233036028996187 := by
  unfold tailWord_2286695
  simp only [CollatzResearch.WordTrace]
  refine ⟨83402618450702026258917539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55601745633801350839278359 83402618450702026258917539)
  ·
    refine ⟨125103927676053039388376309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83402618450702026258917539 125103927676053039388376309)
    ·
      refine ⟨11728493219629972442660279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125103927676053039388376309 11728493219629972442660279)
      ·
        refine ⟨17592739829444958663990419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11728493219629972442660279 17592739829444958663990419)
        ·
          refine ⟨26389109744167437995985629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17592739829444958663990419 26389109744167437995985629)
          ·
            refine ⟨9895916154062789248494611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26389109744167437995985629 9895916154062789248494611)
            ·
              refine ⟨14843874231094183872741917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9895916154062789248494611 14843874231094183872741917)
              ·
                refine ⟨5566452836660318952278219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14843874231094183872741917 5566452836660318952278219)
                ·
                  refine ⟨8349679254990478428417329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5566452836660318952278219 8349679254990478428417329)
                  ·
                    refine ⟨6262259441242858821312997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8349679254990478428417329 6262259441242858821312997)
                    ·
                      refine ⟨1174173645233036028996187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6262259441242858821312997 1174173645233036028996187)
                      ·
                        rfl

theorem cell23_2286695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_2286695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286695 prefixEnd_2286695 := by exact prefixLift 2286695
  have htrace : WordTrace (prefixWord ++ tailWord_2286695) baseStart_2286695 baseEnd_2286695 := by
    simpa [prefixWord, tailWord_2286695, baseEnd_2286695] using wordTrace_append hprefix tailTrace_2286695
  have hstable : (prefixWord ++ tailWord_2286695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286695).length < 2 ^ (prefixWord ++ tailWord_2286695).sum := by decide
  have hdescent : baseEnd_2286695 < baseStart_2286695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286702 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_2286702 : Nat := 118140960795 + 2286702 * 2 ^ 59
def prefixEnd_2286702 : Nat := 4983230072969 + 3 ^ 40 * 2286702 * 2
def baseEnd_2286702 : Nat := 1174177239597617501608655

theorem tailTrace_2286702 : CollatzResearch.WordTrace tailWord_2286702 prefixEnd_2286702 1174177239597617501608655 := by
  unfold tailWord_2286702
  simp only [CollatzResearch.WordTrace]
  refine ⟨10425359220209583306802795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55601915841117777636281573 10425359220209583306802795)
  ·
    refine ⟨15638038830314374960204193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10425359220209583306802795 15638038830314374960204193)
    ·
      refine ⟨11728529122735781220153145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15638038830314374960204193 11728529122735781220153145)
      ·
        refine ⟨8796396842051835915114859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11728529122735781220153145 8796396842051835915114859)
        ·
          refine ⟨13194595263077753872672289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8796396842051835915114859 13194595263077753872672289)
          ·
            refine ⟨9895946447308315404504217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13194595263077753872672289 9895946447308315404504217)
            ·
              refine ⟨7421959835481236553378163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9895946447308315404504217 7421959835481236553378163)
              ·
                refine ⟨11132939753221854830067245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7421959835481236553378163 11132939753221854830067245)
                ·
                  refine ⟨4174852407458195561275217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11132939753221854830067245 4174852407458195561275217)
                  ·
                    refine ⟨3131139305593646670956413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4174852407458195561275217 3131139305593646670956413)
                    ·
                      refine ⟨1174177239597617501608655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3131139305593646670956413 1174177239597617501608655)
                      ·
                        rfl

theorem cell23_2286702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_2286702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286702 prefixEnd_2286702 := by exact prefixLift 2286702
  have htrace : WordTrace (prefixWord ++ tailWord_2286702) baseStart_2286702 baseEnd_2286702 := by
    simpa [prefixWord, tailWord_2286702, baseEnd_2286702] using wordTrace_append hprefix tailTrace_2286702
  have hstable : (prefixWord ++ tailWord_2286702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286702).length < 2 ^ (prefixWord ++ tailWord_2286702).sum := by decide
  have hdescent : baseEnd_2286702 < baseStart_2286702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286716 : List Nat := [2, 2, 2, 1, 1, 3, 4, 3, 1, 2, 2]
def baseStart_2286716 : Nat := 118140960795 + 2286716 * 2 ^ 59
def prefixEnd_2286716 : Nat := 4983230072969 + 3 ^ 40 * 2286716 * 2
def baseEnd_2286716 : Nat := 1174184428326780446833591

theorem tailTrace_2286716 : CollatzResearch.WordTrace tailWord_2286716 prefixEnd_2286716 1174184428326780446833591 := by
  unfold tailWord_2286716
  simp only [CollatzResearch.WordTrace]
  refine ⟨41701692191812973422716001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55602256255750631230288001 41701692191812973422716001)
  ·
    refine ⟨31276269143859730067037001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41701692191812973422716001 31276269143859730067037001)
    ·
      refine ⟨23457201857894797550277751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31276269143859730067037001 23457201857894797550277751)
      ·
        refine ⟨35185802786842196325416627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23457201857894797550277751 35185802786842196325416627)
        ·
          refine ⟨52778704180263294488124941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35185802786842196325416627 52778704180263294488124941)
          ·
            refine ⟨19792014067598735433046853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52778704180263294488124941 19792014067598735433046853)
            ·
              refine ⟨3711002637674762893696285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19792014067598735433046853 3711002637674762893696285)
              ·
                refine ⟨1391625989128036085136107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3711002637674762893696285 1391625989128036085136107)
                ·
                  refine ⟨2087438983692054127704161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391625989128036085136107 2087438983692054127704161)
                  ·
                    refine ⟨1565579237769040595778121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2087438983692054127704161 1565579237769040595778121)
                    ·
                      refine ⟨1174184428326780446833591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1565579237769040595778121 1174184428326780446833591)
                      ·
                        rfl

theorem cell23_2286716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 1, 2, 2].length) (baseStart_2286716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286716 prefixEnd_2286716 := by exact prefixLift 2286716
  have htrace : WordTrace (prefixWord ++ tailWord_2286716) baseStart_2286716 baseEnd_2286716 := by
    simpa [prefixWord, tailWord_2286716, baseEnd_2286716] using wordTrace_append hprefix tailTrace_2286716
  have hstable : (prefixWord ++ tailWord_2286716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286716).length < 2 ^ (prefixWord ++ tailWord_2286716).sum := by decide
  have hdescent : baseEnd_2286716 < baseStart_2286716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286762 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2286762 : Nat := 118140960795 + 2286762 * 2 ^ 59
def prefixEnd_2286762 : Nat := 4983230072969 + 3 ^ 40 * 2286762 * 2
def baseEnd_2286762 : Nat := 1174208048436887266858379

theorem tailTrace_2286762 : CollatzResearch.WordTrace tailWord_2286762 prefixEnd_2286762 1174208048436887266858379 := by
  unfold tailWord_2286762
  simp only [CollatzResearch.WordTrace]
  refine ⟨20851265535364824175401635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55603374760972864467737693 20851265535364824175401635)
  ·
    refine ⟨31276898303047236263102453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20851265535364824175401635 31276898303047236263102453)
    ·
      refine ⟨2932209215910678399665855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31276898303047236263102453 2932209215910678399665855)
      ·
        refine ⟨4398313823866017599498783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2932209215910678399665855 4398313823866017599498783)
        ·
          refine ⟨6597470735799026399248175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4398313823866017599498783 6597470735799026399248175)
          ·
            refine ⟨9896206103698539598872263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6597470735799026399248175 9896206103698539598872263)
            ·
              refine ⟨14844309155547809398308395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9896206103698539598872263 14844309155547809398308395)
              ·
                refine ⟨22266463733321714097462593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14844309155547809398308395 22266463733321714097462593)
                ·
                  refine ⟨16699847799991285573096945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22266463733321714097462593 16699847799991285573096945)
                  ·
                    refine ⟨12524885849993464179822709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16699847799991285573096945 12524885849993464179822709)
                    ·
                      refine ⟨1174208048436887266858379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12524885849993464179822709 1174208048436887266858379)
                      ·
                        rfl

theorem cell23_2286762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2286762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286762 prefixEnd_2286762 := by exact prefixLift 2286762
  have htrace : WordTrace (prefixWord ++ tailWord_2286762) baseStart_2286762 baseEnd_2286762 := by
    simpa [prefixWord, tailWord_2286762, baseEnd_2286762] using wordTrace_append hprefix tailTrace_2286762
  have hstable : (prefixWord ++ tailWord_2286762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286762).length < 2 ^ (prefixWord ++ tailWord_2286762).sum := by decide
  have hdescent : baseEnd_2286762 < baseStart_2286762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286775 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 5]
def baseStart_2286775 : Nat := 118140960795 + 2286775 * 2 ^ 59
def prefixEnd_2286775 : Nat := 4983230072969 + 3 ^ 40 * 2286775 * 2
def baseEnd_2286775 : Nat := 1174214723685395715995819

theorem tailTrace_2286775 : CollatzResearch.WordTrace tailWord_2286775 prefixEnd_2286775 1174214723685395715995819 := by
  unfold tailWord_2286775
  simp only [CollatzResearch.WordTrace]
  refine ⟨83405536290412199921829779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55603690860274799947886519 83405536290412199921829779)
  ·
    refine ⟨125108304435618299882744669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83405536290412199921829779 125108304435618299882744669)
    ·
      refine ⟨46915614163356862456029251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125108304435618299882744669 46915614163356862456029251)
      ·
        refine ⟨70373421245035293684043877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46915614163356862456029251 70373421245035293684043877)
        ·
          refine ⟨13195016483444117565758227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70373421245035293684043877 13195016483444117565758227)
          ·
            refine ⟨19792524725166176348637341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13195016483444117565758227 19792524725166176348637341)
            ·
              refine ⟨7422196771937316130739003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19792524725166176348637341 7422196771937316130739003)
              ·
                refine ⟨11133295157905974196108505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7422196771937316130739003 11133295157905974196108505)
                ·
                  refine ⟨8349971368429480647081379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11133295157905974196108505 8349971368429480647081379)
                  ·
                    refine ⟨12524957052644220970622069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8349971368429480647081379 12524957052644220970622069)
                    ·
                      refine ⟨1174214723685395715995819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12524957052644220970622069 1174214723685395715995819)
                      ·
                        rfl

theorem cell23_2286775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_2286775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286775 prefixEnd_2286775 := by exact prefixLift 2286775
  have htrace : WordTrace (prefixWord ++ tailWord_2286775) baseStart_2286775 baseEnd_2286775 := by
    simpa [prefixWord, tailWord_2286775, baseEnd_2286775] using wordTrace_append hprefix tailTrace_2286775
  have hstable : (prefixWord ++ tailWord_2286775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286775).length < 2 ^ (prefixWord ++ tailWord_2286775).sum := by decide
  have hdescent : baseEnd_2286775 < baseStart_2286775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286789 : List Nat := [1, 3, 1, 1, 1, 1, 3, 6, 2, 2, 2]
def baseStart_2286789 : Nat := 118140960795 + 2286789 * 2 ^ 59
def prefixEnd_2286789 : Nat := 4983230072969 + 3 ^ 40 * 2286789 * 2
def baseEnd_2286789 : Nat := 1174221912414558661220755

theorem tailTrace_2286789 : CollatzResearch.WordTrace tailWord_2286789 prefixEnd_2286789 1174221912414558661220755 := by
  unfold tailWord_2286789
  simp only [CollatzResearch.WordTrace]
  refine ⟨83406046912361480312839421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55604031274907653541892947 83406046912361480312839421)
  ·
    refine ⟨31277267592135555117314783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83406046912361480312839421 31277267592135555117314783)
    ·
      refine ⟨46915901388203332675972175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31277267592135555117314783 46915901388203332675972175)
      ·
        refine ⟨70373852082304999013958263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46915901388203332675972175 70373852082304999013958263)
        ·
          refine ⟨105560778123457498520937395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70373852082304999013958263 105560778123457498520937395)
          ·
            refine ⟨158341167185186247781406093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105560778123457498520937395 158341167185186247781406093)
            ·
              refine ⟨59377937694444842918027285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158341167185186247781406093 59377937694444842918027285)
              ·
                refine ⟨2783340829427102011782529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59377937694444842918027285 2783340829427102011782529)
                ·
                  refine ⟨2087505622070326508836897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2783340829427102011782529 2087505622070326508836897)
                  ·
                    refine ⟨1565629216552744881627673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2087505622070326508836897 1565629216552744881627673)
                    ·
                      refine ⟨1174221912414558661220755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1565629216552744881627673 1174221912414558661220755)
                      ·
                        rfl

theorem cell23_2286789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 2, 2].length) (baseStart_2286789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286789 prefixEnd_2286789 := by exact prefixLift 2286789
  have htrace : WordTrace (prefixWord ++ tailWord_2286789) baseStart_2286789 baseEnd_2286789 := by
    simpa [prefixWord, tailWord_2286789, baseEnd_2286789] using wordTrace_append hprefix tailTrace_2286789
  have hstable : (prefixWord ++ tailWord_2286789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286789).length < 2 ^ (prefixWord ++ tailWord_2286789).sum := by decide
  have hdescent : baseEnd_2286789 < baseStart_2286789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286835 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 5]
def baseStart_2286835 : Nat := 118140960795 + 2286835 * 2 ^ 59
def prefixEnd_2286835 : Nat := 4983230072969 + 3 ^ 40 * 2286835 * 2
def baseEnd_2286835 : Nat := 1174245532524665481245543

theorem tailTrace_2286835 : CollatzResearch.WordTrace tailWord_2286835 prefixEnd_2286835 1174245532524665481245543 := by
  unfold tailWord_2286835
  simp only [CollatzResearch.WordTrace]
  refine ⟨83407724670194830169013959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55605149780129886779342639 83407724670194830169013959)
  ·
    refine ⟨125111587005292245253520939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83407724670194830169013959 125111587005292245253520939)
    ·
      refine ⟨187667380507938367880281409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125111587005292245253520939 187667380507938367880281409)
      ·
        refine ⟨140750535380953775910211057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187667380507938367880281409 140750535380953775910211057)
        ·
          refine ⟨105562901535715331932658293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140750535380953775910211057 105562901535715331932658293)
          ·
            refine ⟨9896522018973312368686715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105562901535715331932658293 9896522018973312368686715)
            ·
              refine ⟨14844783028459968553030073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9896522018973312368686715 14844783028459968553030073)
              ·
                refine ⟨11133587271344976414772555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14844783028459968553030073 11133587271344976414772555)
                ·
                  refine ⟨16700380907017464622158833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11133587271344976414772555 16700380907017464622158833)
                  ·
                    refine ⟨12525285680263098466619125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16700380907017464622158833 12525285680263098466619125)
                    ·
                      refine ⟨1174245532524665481245543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12525285680263098466619125 1174245532524665481245543)
                      ·
                        rfl

theorem cell23_2286835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_2286835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286835 prefixEnd_2286835 := by exact prefixLift 2286835
  have htrace : WordTrace (prefixWord ++ tailWord_2286835) baseStart_2286835 baseEnd_2286835 := by
    simpa [prefixWord, tailWord_2286835, baseEnd_2286835] using wordTrace_append hprefix tailTrace_2286835
  have hstable : (prefixWord ++ tailWord_2286835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286835).length < 2 ^ (prefixWord ++ tailWord_2286835).sum := by decide
  have hdescent : baseEnd_2286835 < baseStart_2286835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286845 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_2286845 : Nat := 118140960795 + 2286845 * 2 ^ 59
def prefixEnd_2286845 : Nat := 4983230072969 + 3 ^ 40 * 2286845 * 2
def baseEnd_2286845 : Nat := 1174250667331210442120497

theorem tailTrace_2286845 : CollatzResearch.WordTrace tailWord_2286845 prefixEnd_2286845 1174250667331210442120497 := by
  unfold tailWord_2286845
  simp only [CollatzResearch.WordTrace]
  refine ⟨83408089400158601876877989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55605392933439067917918659 83408089400158601876877989)
  ·
    refine ⟨15639016762529737851914623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83408089400158601876877989 15639016762529737851914623)
    ·
      refine ⟨23458525143794606777871935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15639016762529737851914623 23458525143794606777871935)
      ·
        refine ⟨35187787715691910166807903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23458525143794606777871935 35187787715691910166807903)
        ·
          refine ⟨52781681573537865250211855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35187787715691910166807903 52781681573537865250211855)
          ·
            refine ⟨79172522360306797875317783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52781681573537865250211855 79172522360306797875317783)
            ·
              refine ⟨118758783540460196812976675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79172522360306797875317783 118758783540460196812976675)
              ·
                refine ⟨178138175310690295219465013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118758783540460196812976675 178138175310690295219465013)
                ·
                  refine ⟨16700453935377215176824845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 178138175310690295219465013 16700453935377215176824845)
                  ·
                    refine ⟨6262670225766455691309317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16700453935377215176824845 6262670225766455691309317)
                    ·
                      refine ⟨1174250667331210442120497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6262670225766455691309317 1174250667331210442120497)
                      ·
                        rfl

theorem cell23_2286845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_2286845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286845 prefixEnd_2286845 := by exact prefixLift 2286845
  have htrace : WordTrace (prefixWord ++ tailWord_2286845) baseStart_2286845 baseEnd_2286845 := by
    simpa [prefixWord, tailWord_2286845, baseEnd_2286845] using wordTrace_append hprefix tailTrace_2286845
  have hstable : (prefixWord ++ tailWord_2286845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286845).length < 2 ^ (prefixWord ++ tailWord_2286845).sum := by decide
  have hdescent : baseEnd_2286845 < baseStart_2286845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286846 : List Nat := [4, 2, 2, 1, 1, 2, 4, 2, 5]
def baseStart_2286846 : Nat := 118140960795 + 2286846 * 2 ^ 59
def prefixEnd_2286846 : Nat := 4983230072969 + 3 ^ 40 * 2286846 * 2
def baseEnd_2286846 : Nat := 130472353423540548689777

theorem tailTrace_2286846 : CollatzResearch.WordTrace tailWord_2286846 prefixEnd_2286846 130472353423540548689777 := by
  unfold tailWord_2286846
  simp only [CollatzResearch.WordTrace]
  refine ⟨10426015734144372380958049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55605417248769986031776261 10426015734144372380958049)
  ·
    refine ⟨7819511800608279285718537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10426015734144372380958049 7819511800608279285718537)
    ·
      refine ⟨5864633850456209464288903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7819511800608279285718537 5864633850456209464288903)
      ·
        refine ⟨8796950775684314196433355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5864633850456209464288903 8796950775684314196433355)
        ·
          refine ⟨13195426163526471294650033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8796950775684314196433355 13195426163526471294650033)
          ·
            refine ⟨9896569622644853470987525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13195426163526471294650033 9896569622644853470987525)
            ·
              refine ⟨1855606804245910025810161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9896569622644853470987525 1855606804245910025810161)
              ·
                refine ⟨1391705103184432519357621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1855606804245910025810161 1391705103184432519357621)
                ·
                  refine ⟨130472353423540548689777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1391705103184432519357621 130472353423540548689777)
                  ·
                    rfl

theorem cell23_2286846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_2286846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286846 prefixEnd_2286846 := by exact prefixLift 2286846
  have htrace : WordTrace (prefixWord ++ tailWord_2286846) baseStart_2286846 baseEnd_2286846 := by
    simpa [prefixWord, tailWord_2286846, baseEnd_2286846] using wordTrace_append hprefix tailTrace_2286846
  have hstable : (prefixWord ++ tailWord_2286846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286846).length < 2 ^ (prefixWord ++ tailWord_2286846).sum := by decide
  have hdescent : baseEnd_2286846 < baseStart_2286846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286852 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_2286852 : Nat := 118140960795 + 2286852 * 2 ^ 59
def prefixEnd_2286852 : Nat := 4983230072969 + 3 ^ 40 * 2286852 * 2
def baseEnd_2286852 : Nat := 1174254261695791914732965

theorem tailTrace_2286852 : CollatzResearch.WordTrace tailWord_2286852 prefixEnd_2286852 1174254261695791914732965 := by
  unfold tailWord_2286852
  simp only [CollatzResearch.WordTrace]
  refine ⟨41704172355566621036191405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55605563140755494714921873 41704172355566621036191405)
  ·
    refine ⟨15639064633337482888571777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41704172355566621036191405 15639064633337482888571777)
    ·
      refine ⟨11729298475003112166428833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15639064633337482888571777 11729298475003112166428833)
      ·
        refine ⟨8796973856252334124821625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11729298475003112166428833 8796973856252334124821625)
        ·
          refine ⟨6597730392189250593616219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8796973856252334124821625 6597730392189250593616219)
          ·
            refine ⟨9896595588283875890424329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6597730392189250593616219 9896595588283875890424329)
            ·
              refine ⟨7422446691212906917818247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9896595588283875890424329 7422446691212906917818247)
              ·
                refine ⟨11133670036819360376727371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7422446691212906917818247 11133670036819360376727371)
                ·
                  refine ⟨16700505055229040565091057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11133670036819360376727371 16700505055229040565091057)
                  ·
                    refine ⟨12525378791421780423818293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16700505055229040565091057 12525378791421780423818293)
                    ·
                      refine ⟨1174254261695791914732965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12525378791421780423818293 1174254261695791914732965)
                      ·
                        rfl

theorem cell23_2286852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_2286852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286852 prefixEnd_2286852 := by exact prefixLift 2286852
  have htrace : WordTrace (prefixWord ++ tailWord_2286852) baseStart_2286852 baseEnd_2286852 := by
    simpa [prefixWord, tailWord_2286852, baseEnd_2286852] using wordTrace_append hprefix tailTrace_2286852
  have hstable : (prefixWord ++ tailWord_2286852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286852).length < 2 ^ (prefixWord ++ tailWord_2286852).sum := by decide
  have hdescent : baseEnd_2286852 < baseStart_2286852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286872 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 5, 4]
def baseStart_2286872 : Nat := 118140960795 + 2286872 * 2 ^ 59
def prefixEnd_2286872 : Nat := 4983230072969 + 3 ^ 40 * 2286872 * 2
def baseEnd_2286872 : Nat := 391421510436293945494291

theorem tailTrace_2286872 : CollatzResearch.WordTrace tailWord_2286872 prefixEnd_2286872 391421510436293945494291 := by
  unfold tailWord_2286872
  simp only [CollatzResearch.WordTrace]
  refine ⟨41704537085530392744055435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55606049447373856992073913 41704537085530392744055435)
  ·
    refine ⟨62556805628295589116083153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41704537085530392744055435 62556805628295589116083153)
    ·
      refine ⟨46917604221221691837062365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62556805628295589116083153 46917604221221691837062365)
      ·
        refine ⟨17594101582958134438898387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46917604221221691837062365 17594101582958134438898387)
        ·
          refine ⟨26391152374437201658347581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17594101582958134438898387 26391152374437201658347581)
          ·
            refine ⟨9896682140413950621880343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26391152374437201658347581 9896682140413950621880343)
            ·
              refine ⟨14845023210620925932820515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9896682140413950621880343 14845023210620925932820515)
              ·
                refine ⟨22267534815931388899230773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14845023210620925932820515 22267534815931388899230773)
                ·
                  refine ⟨2087581388993567709302885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22267534815931388899230773 2087581388993567709302885)
                  ·
                    refine ⟨391421510436293945494291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2087581388993567709302885 391421510436293945494291)
                    ·
                      rfl

theorem cell23_2286872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_2286872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286872 prefixEnd_2286872 := by exact prefixLift 2286872
  have htrace : WordTrace (prefixWord ++ tailWord_2286872) baseStart_2286872 baseEnd_2286872 := by
    simpa [prefixWord, tailWord_2286872, baseEnd_2286872] using wordTrace_append hprefix tailTrace_2286872
  have hstable : (prefixWord ++ tailWord_2286872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286872).length < 2 ^ (prefixWord ++ tailWord_2286872).sum := by decide
  have hdescent : baseEnd_2286872 < baseStart_2286872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286919 : List Nat := [1, 1, 4, 1, 2, 4, 3, 1, 6]
def baseStart_2286919 : Nat := 118140960795 + 2286919 * 2 ^ 59
def prefixEnd_2286919 : Nat := 4983230072969 + 3 ^ 40 * 2286919 * 2
def baseEnd_2286919 : Nat := 130476518322182572510573

theorem tailTrace_2286919 : CollatzResearch.WordTrace tailWord_2286919 prefixEnd_2286919 130476518322182572510573 := by
  unfold tailWord_2286919
  simp only [CollatzResearch.WordTrace]
  refine ⟨83410788401890512515071811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55607192267927008343381207 83410788401890512515071811)
  ·
    refine ⟨125116182602835768772607717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83410788401890512515071811 125116182602835768772607717)
    ·
      refine ⟨23459284238031706644863947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125116182602835768772607717 23459284238031706644863947)
      ·
        refine ⟨35188926357047559967295921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23459284238031706644863947 35188926357047559967295921)
        ·
          refine ⟨26391694767785669975471941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35188926357047559967295921 26391694767785669975471941)
          ·
            refine ⟨4948442768959813120400989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26391694767785669975471941 4948442768959813120400989)
            ·
              refine ⟨1855666038359929920150371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4948442768959813120400989 1855666038359929920150371)
              ·
                refine ⟨2783499057539894880225557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1855666038359929920150371 2783499057539894880225557)
                ·
                  refine ⟨130476518322182572510573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2783499057539894880225557 130476518322182572510573)
                  ·
                    rfl

theorem cell23_2286919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 6].length) (baseStart_2286919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286919 prefixEnd_2286919 := by exact prefixLift 2286919
  have htrace : WordTrace (prefixWord ++ tailWord_2286919) baseStart_2286919 baseEnd_2286919 := by
    simpa [prefixWord, tailWord_2286919, baseEnd_2286919] using wordTrace_append hprefix tailTrace_2286919
  have hstable : (prefixWord ++ tailWord_2286919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286919).length < 2 ^ (prefixWord ++ tailWord_2286919).sum := by decide
  have hdescent : baseEnd_2286919 < baseStart_2286919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286929 : List Nat := [1, 2, 2, 1, 4, 1, 1, 4, 3, 1, 3]
def baseStart_2286929 : Nat := 118140960795 + 2286929 * 2 ^ 59
def prefixEnd_2286929 : Nat := 4983230072969 + 3 ^ 40 * 2286929 * 2
def baseEnd_2286929 : Nat := 1174293799706188113470111

theorem tailTrace_2286929 : CollatzResearch.WordTrace tailWord_2286929 prefixEnd_2286929 1174293799706188113470111 := by
  unfold tailWord_2286929
  simp only [CollatzResearch.WordTrace]
  refine ⟨83411153131854284222935841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55607435421236189481957227 83411153131854284222935841)
  ·
    refine ⟨62558364848890713167201881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83411153131854284222935841 62558364848890713167201881)
    ·
      refine ⟨46918773636668034875401411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62558364848890713167201881 46918773636668034875401411)
      ·
        refine ⟨70378160455002052313102117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46918773636668034875401411 70378160455002052313102117)
        ·
          refine ⟨13195905085312884808706647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70378160455002052313102117 13195905085312884808706647)
          ·
            refine ⟨19793857627969327213059971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13195905085312884808706647 19793857627969327213059971)
            ·
              refine ⟨29690786441953990819589957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19793857627969327213059971 29690786441953990819589957)
              ·
                refine ⟨5567022457866373278673117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29690786441953990819589957 5567022457866373278673117)
                ·
                  refine ⟨2087633421699889979502419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5567022457866373278673117 2087633421699889979502419)
                  ·
                    refine ⟨3131450132549834969253629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2087633421699889979502419 3131450132549834969253629)
                    ·
                      refine ⟨1174293799706188113470111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3131450132549834969253629 1174293799706188113470111)
                      ·
                        rfl

theorem cell23_2286929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 1, 3].length) (baseStart_2286929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286929 prefixEnd_2286929 := by exact prefixLift 2286929
  have htrace : WordTrace (prefixWord ++ tailWord_2286929) baseStart_2286929 baseEnd_2286929 := by
    simpa [prefixWord, tailWord_2286929, baseEnd_2286929] using wordTrace_append hprefix tailTrace_2286929
  have hstable : (prefixWord ++ tailWord_2286929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286929).length < 2 ^ (prefixWord ++ tailWord_2286929).sum := by decide
  have hdescent : baseEnd_2286929 < baseStart_2286929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286956 : List Nat := [2, 2, 1, 1, 5, 2, 1, 2, 2, 3, 2]
def baseStart_2286956 : Nat := 118140960795 + 2286956 * 2 ^ 59
def prefixEnd_2286956 : Nat := 4983230072969 + 3 ^ 40 * 2286956 * 2
def baseEnd_2286956 : Nat := 1174307663683859507832487

theorem tailTrace_2286956 : CollatzResearch.WordTrace tailWord_2286956 prefixEnd_2286956 1174307663683859507832487 := by
  unfold tailWord_2286956
  simp only [CollatzResearch.WordTrace]
  refine ⟨41706068951378233917084361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55608091935170978556112481 41706068951378233917084361)
  ·
    refine ⟨31279551713533675437813271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41706068951378233917084361 31279551713533675437813271)
    ·
      refine ⟨46919327570300513156719907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31279551713533675437813271 46919327570300513156719907)
      ·
        refine ⟨70378991355450769735079861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46919327570300513156719907 70378991355450769735079861)
        ·
          refine ⟨6598030439573509662663737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70378991355450769735079861 6598030439573509662663737)
          ·
            refine ⟨4948522829680132246997803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6598030439573509662663737 4948522829680132246997803)
            ·
              refine ⟨7422784244520198370496705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4948522829680132246997803 7422784244520198370496705)
              ·
                refine ⟨5567088183390148777872529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7422784244520198370496705 5567088183390148777872529)
                ·
                  refine ⟨4175316137542611583404397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5567088183390148777872529 4175316137542611583404397)
                  ·
                    refine ⟨1565743551578479343776649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4175316137542611583404397 1565743551578479343776649)
                    ·
                      refine ⟨1174307663683859507832487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1565743551578479343776649 1174307663683859507832487)
                      ·
                        rfl

theorem cell23_2286956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 3, 2].length) (baseStart_2286956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286956 prefixEnd_2286956 := by exact prefixLift 2286956
  have htrace : WordTrace (prefixWord ++ tailWord_2286956) baseStart_2286956 baseEnd_2286956 := by
    simpa [prefixWord, tailWord_2286956, baseEnd_2286956] using wordTrace_append hprefix tailTrace_2286956
  have hstable : (prefixWord ++ tailWord_2286956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286956).length < 2 ^ (prefixWord ++ tailWord_2286956).sum := by decide
  have hdescent : baseEnd_2286956 < baseStart_2286956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286972 : List Nat := [2, 2, 2, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_2286972 : Nat := 118140960795 + 2286972 * 2 ^ 59
def prefixEnd_2286972 : Nat := 4983230072969 + 3 ^ 40 * 2286972 * 2
def baseEnd_2286972 : Nat := 1174315879374331445232413

theorem tailTrace_2286972 : CollatzResearch.WordTrace tailWord_2286972 prefixEnd_2286972 1174315879374331445232413 := by
  unfold tailWord_2286972
  simp only [CollatzResearch.WordTrace]
  refine ⟨41706360735349251283375585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55608480980465668377834113 41706360735349251283375585)
  ·
    refine ⟨31279770551511938462531689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41706360735349251283375585 31279770551511938462531689)
    ·
      refine ⟨23459827913633953846898767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31279770551511938462531689 23459827913633953846898767)
      ·
        refine ⟨35189741870450930770348151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23459827913633953846898767 35189741870450930770348151)
        ·
          refine ⟨52784612805676396155522227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35189741870450930770348151 52784612805676396155522227)
          ·
            refine ⟨79176919208514594233283341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52784612805676396155522227 79176919208514594233283341)
            ·
              refine ⟨29691344703192972837481253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79176919208514594233283341 29691344703192972837481253)
              ·
                refine ⟨5567127131848682407027735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29691344703192972837481253 5567127131848682407027735)
                ·
                  refine ⟨8350690697773023610541603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5567127131848682407027735 8350690697773023610541603)
                  ·
                    refine ⟨12526036046659535415812405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8350690697773023610541603 12526036046659535415812405)
                    ·
                      refine ⟨1174315879374331445232413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12526036046659535415812405 1174315879374331445232413)
                      ·
                        rfl

theorem cell23_2286972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_2286972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2286972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2286972 prefixEnd_2286972 := by exact prefixLift 2286972
  have htrace : WordTrace (prefixWord ++ tailWord_2286972) baseStart_2286972 baseEnd_2286972 := by
    simpa [prefixWord, tailWord_2286972, baseEnd_2286972] using wordTrace_append hprefix tailTrace_2286972
  have hstable : (prefixWord ++ tailWord_2286972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286972).length < 2 ^ (prefixWord ++ tailWord_2286972).sum := by decide
  have hdescent : baseEnd_2286972 < baseStart_2286972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287020 : List Nat := [2, 2, 1, 1, 1, 1, 8, 2, 1, 2, 2]
def baseStart_2287020 : Nat := 118140960795 + 2287020 * 2 ^ 59
def prefixEnd_2287020 : Nat := 4983230072969 + 3 ^ 40 * 2287020 * 2
def baseEnd_2287020 : Nat := 1174340526445747257432193

theorem tailTrace_2287020 : CollatzResearch.WordTrace tailWord_2287020 prefixEnd_2287020 1174340526445747257432193 := by
  unfold tailWord_2287020
  simp only [CollatzResearch.WordTrace]
  refine ⟨41707236087262303382249257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55609648116349737842999009 41707236087262303382249257)
  ·
    refine ⟨31280427065446727536686943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41707236087262303382249257 31280427065446727536686943)
    ·
      refine ⟨46920640598170091305030415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31280427065446727536686943 46920640598170091305030415)
      ·
        refine ⟨70380960897255136957545623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46920640598170091305030415 70380960897255136957545623)
        ·
          refine ⟨105571441345882705436318435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70380960897255136957545623 105571441345882705436318435)
          ·
            refine ⟨158357162018824058154477653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105571441345882705436318435 158357162018824058154477653)
            ·
              refine ⟨1855747992408094431497785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 158357162018824058154477653 1855747992408094431497785)
              ·
                refine ⟨1391810994306070823623339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1855747992408094431497785 1391810994306070823623339)
                ·
                  refine ⟨2087716491459106235435009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391810994306070823623339 2087716491459106235435009)
                  ·
                    refine ⟨1565787368594329676576257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2087716491459106235435009 1565787368594329676576257)
                    ·
                      refine ⟨1174340526445747257432193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1565787368594329676576257 1174340526445747257432193)
                      ·
                        rfl

theorem cell23_2287020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 1, 2, 2].length) (baseStart_2287020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287020 prefixEnd_2287020 := by exact prefixLift 2287020
  have htrace : WordTrace (prefixWord ++ tailWord_2287020) baseStart_2287020 baseEnd_2287020 := by
    simpa [prefixWord, tailWord_2287020, baseEnd_2287020] using wordTrace_append hprefix tailTrace_2287020
  have hstable : (prefixWord ++ tailWord_2287020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287020).length < 2 ^ (prefixWord ++ tailWord_2287020).sum := by decide
  have hdescent : baseEnd_2287020 < baseStart_2287020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287069 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 2, 6]
def baseStart_2287069 : Nat := 118140960795 + 2287069 * 2 ^ 59
def prefixEnd_2287069 : Nat := 4983230072969 + 3 ^ 40 * 2287069 * 2
def baseEnd_2287069 : Nat := 391455228999272521906489

theorem tailTrace_2287069 : CollatzResearch.WordTrace tailWord_2287069 prefixEnd_2287069 391455228999272521906489 := by
  unfold tailWord_2287069
  simp only [CollatzResearch.WordTrace]
  refine ⟨83416259351347088133032261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55610839567564725422021507 83416259351347088133032261)
  ·
    refine ⟨15640548628377579024943549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83416259351347088133032261 15640548628377579024943549)
    ·
      refine ⟨5865205735641592134353831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15640548628377579024943549 5865205735641592134353831)
      ·
        refine ⟨8797808603462388201530747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5865205735641592134353831 8797808603462388201530747)
        ·
          refine ⟨13196712905193582302296121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8797808603462388201530747 13196712905193582302296121)
          ·
            refine ⟨9897534678895186726722091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13196712905193582302296121 9897534678895186726722091)
            ·
              refine ⟨14846302018342780090083137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9897534678895186726722091 14846302018342780090083137)
              ·
                refine ⟨11134726513757085067562353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14846302018342780090083137 11134726513757085067562353)
                ·
                  refine ⟨8351044885317813800671765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11134726513757085067562353 8351044885317813800671765)
                  ·
                    refine ⟨391455228999272521906489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8351044885317813800671765 391455228999272521906489)
                    ·
                      rfl

theorem cell23_2287069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_2287069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287069 prefixEnd_2287069 := by exact prefixLift 2287069
  have htrace : WordTrace (prefixWord ++ tailWord_2287069) baseStart_2287069 baseEnd_2287069 := by
    simpa [prefixWord, tailWord_2287069, baseEnd_2287069] using wordTrace_append hprefix tailTrace_2287069
  have hstable : (prefixWord ++ tailWord_2287069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287069).length < 2 ^ (prefixWord ++ tailWord_2287069).sum := by decide
  have hdescent : baseEnd_2287069 < baseStart_2287069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287089 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 2, 2, 4]
def baseStart_2287089 : Nat := 118140960795 + 2287089 * 2 ^ 59
def prefixEnd_2287089 : Nat := 4983230072969 + 3 ^ 40 * 2287089 * 2
def baseEnd_2287089 : Nat := 1174375956610907487469375

theorem tailTrace_2287089 : CollatzResearch.WordTrace tailWord_2287089 prefixEnd_2287089 1174375956610907487469375 := by
  unfold tailWord_2287089
  simp only [CollatzResearch.WordTrace]
  refine ⟨83416988811274631548760321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55611325874183087699173547 83416988811274631548760321)
  ·
    refine ⟨62562741608455973661570241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83416988811274631548760321 62562741608455973661570241)
    ·
      refine ⟨46922056206341980246177681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62562741608455973661570241 46922056206341980246177681)
      ·
        refine ⟨35191542154756485184633261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46922056206341980246177681 35191542154756485184633261)
        ·
          refine ⟨13196828308033681944237473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35191542154756485184633261 13196828308033681944237473)
          ·
            refine ⟨9897621231025261458178105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13196828308033681944237473 9897621231025261458178105)
            ·
              refine ⟨7423215923268946093633579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9897621231025261458178105 7423215923268946093633579)
              ·
                refine ⟨11134823884903419140450369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7423215923268946093633579 11134823884903419140450369)
                ·
                  refine ⟨8351117913677564355337777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11134823884903419140450369 8351117913677564355337777)
                  ·
                    refine ⟨6263338435258173266503333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8351117913677564355337777 6263338435258173266503333)
                    ·
                      refine ⟨1174375956610907487469375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6263338435258173266503333 1174375956610907487469375)
                      ·
                        rfl

theorem cell23_2287089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_2287089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287089 prefixEnd_2287089 := by exact prefixLift 2287089
  have htrace : WordTrace (prefixWord ++ tailWord_2287089) baseStart_2287089 baseEnd_2287089 := by
    simpa [prefixWord, tailWord_2287089, baseEnd_2287089] using wordTrace_append hprefix tailTrace_2287089
  have hstable : (prefixWord ++ tailWord_2287089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287089).length < 2 ^ (prefixWord ++ tailWord_2287089).sum := by decide
  have hdescent : baseEnd_2287089 < baseStart_2287089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287133 : List Nat := [1, 4, 2, 2, 1, 1, 5, 2, 5]
def baseStart_2287133 : Nat := 118140960795 + 2287133 * 2 ^ 59
def prefixEnd_2287133 : Nat := 4983230072969 + 3 ^ 40 * 2287133 * 2
def baseEnd_2287133 : Nat := 130488727751078368368797

theorem tailTrace_2287133 : CollatzResearch.WordTrace tailWord_2287133 prefixEnd_2287133 130488727751078368368797 := by
  unfold tailWord_2287133
  simp only [CollatzResearch.WordTrace]
  refine ⟨83418593623115227063362053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55612395748743484708908035 83418593623115227063362053)
  ·
    refine ⟨15640986304334105074380385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83418593623115227063362053 15640986304334105074380385)
    ·
      refine ⟨11730739728250578805785289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15640986304334105074380385 11730739728250578805785289)
      ·
        refine ⟨8798054796187934104338967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11730739728250578805785289 8798054796187934104338967)
        ·
          refine ⟨13197082194281901156508451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8798054796187934104338967 13197082194281901156508451)
          ·
            refine ⟨19795623291422851734762677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13197082194281901156508451 19795623291422851734762677)
            ·
              refine ⟨1855839683570892350134001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19795623291422851734762677 1855839683570892350134001)
              ·
                refine ⟨1391879762678169262600501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1855839683570892350134001 1391879762678169262600501)
                ·
                  refine ⟨130488727751078368368797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1391879762678169262600501 130488727751078368368797)
                  ·
                    rfl

theorem cell23_2287133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_2287133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287133 prefixEnd_2287133 := by exact prefixLift 2287133
  have htrace : WordTrace (prefixWord ++ tailWord_2287133) baseStart_2287133 baseEnd_2287133 := by
    simpa [prefixWord, tailWord_2287133, baseEnd_2287133] using wordTrace_append hprefix tailTrace_2287133
  have hstable : (prefixWord ++ tailWord_2287133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287133).length < 2 ^ (prefixWord ++ tailWord_2287133).sum := by decide
  have hdescent : baseEnd_2287133 < baseStart_2287133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287144 : List Nat := [2, 1, 5, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_2287144 : Nat := 118140960795 + 2287144 * 2 ^ 59
def prefixEnd_2287144 : Nat := 4983230072969 + 3 ^ 40 * 2287144 * 2
def baseEnd_2287144 : Nat := 1174404198046904772281623

theorem tailTrace_2287144 : CollatzResearch.WordTrace tailWord_2287144 prefixEnd_2287144 1174404198046904772281623 := by
  unfold tailWord_2287144
  simp only [CollatzResearch.WordTrace]
  refine ⟨41709497413037687971006243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55612663217383583961341657 41709497413037687971006243)
  ·
    refine ⟨62564246119556531956509365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41709497413037687971006243 62564246119556531956509365)
    ·
      refine ⟨5865398073708424870922753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62564246119556531956509365 5865398073708424870922753)
      ·
        refine ⟨4399048555281318653192065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5865398073708424870922753 4399048555281318653192065)
        ·
          refine ⟨3299286416460988989894049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4399048555281318653192065 3299286416460988989894049)
          ·
            refine ⟨2474464812345741742420537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3299286416460988989894049 2474464812345741742420537)
            ·
              refine ⟨1855848609259306306815403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2474464812345741742420537 1855848609259306306815403)
              ·
                refine ⟨2783772913888959460223105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1855848609259306306815403 2783772913888959460223105)
                ·
                  refine ⟨2087829685416719595167329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2783772913888959460223105 2087829685416719595167329)
                  ·
                    refine ⟨1565872264062539696375497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2087829685416719595167329 1565872264062539696375497)
                    ·
                      refine ⟨1174404198046904772281623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1565872264062539696375497 1174404198046904772281623)
                      ·
                        rfl

theorem cell23_2287144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_2287144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287144 prefixEnd_2287144 := by exact prefixLift 2287144
  have htrace : WordTrace (prefixWord ++ tailWord_2287144) baseStart_2287144 baseEnd_2287144 := by
    simpa [prefixWord, tailWord_2287144, baseEnd_2287144] using wordTrace_append hprefix tailTrace_2287144
  have hstable : (prefixWord ++ tailWord_2287144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287144).length < 2 ^ (prefixWord ++ tailWord_2287144).sum := by decide
  have hdescent : baseEnd_2287144 < baseStart_2287144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287199 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 3]
def baseStart_2287199 : Nat := 118140960795 + 2287199 * 2 ^ 59
def prefixEnd_2287199 : Nat := 4983230072969 + 3 ^ 40 * 2287199 * 2
def baseEnd_2287199 : Nat := 1174432439482902057093869

theorem tailTrace_2287199 : CollatzResearch.WordTrace tailWord_2287199 prefixEnd_2287199 1174432439482902057093869 := by
  unfold tailWord_2287199
  simp only [CollatzResearch.WordTrace]
  refine ⟨83421000840876120335264651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55614000560584080223509767 83421000840876120335264651)
  ·
    refine ⟨125131501261314180502896977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83421000840876120335264651 125131501261314180502896977)
    ·
      refine ⟨93848625945985635377172733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125131501261314180502896977 93848625945985635377172733)
      ·
        refine ⟨35193234729744613266439775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93848625945985635377172733 35193234729744613266439775)
        ·
          refine ⟨52789852094616919899659663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35193234729744613266439775 52789852094616919899659663)
          ·
            refine ⟨79184778141925379849489495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52789852094616919899659663 79184778141925379849489495)
            ·
              refine ⟨118777167212888069774234243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79184778141925379849489495 118777167212888069774234243)
              ·
                refine ⟨178165750819332104661351365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118777167212888069774234243 178165750819332104661351365)
                ·
                  refine ⟨33406078278624769624003381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 178165750819332104661351365 33406078278624769624003381)
                  ·
                    refine ⟨3131819838621072152250317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33406078278624769624003381 3131819838621072152250317)
                    ·
                      refine ⟨1174432439482902057093869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3131819838621072152250317 1174432439482902057093869)
                      ·
                        rfl

theorem cell23_2287199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_2287199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287199 prefixEnd_2287199 := by exact prefixLift 2287199
  have htrace : WordTrace (prefixWord ++ tailWord_2287199) baseStart_2287199 baseEnd_2287199 := by
    simpa [prefixWord, tailWord_2287199, baseEnd_2287199] using wordTrace_append hprefix tailTrace_2287199
  have hstable : (prefixWord ++ tailWord_2287199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287199).length < 2 ^ (prefixWord ++ tailWord_2287199).sum := by decide
  have hdescent : baseEnd_2287199 < baseStart_2287199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287240 : List Nat := [2, 1, 3, 5, 1, 2, 1, 2, 6]
def baseStart_2287240 : Nat := 118140960795 + 2287240 * 2 ^ 59
def prefixEnd_2287240 : Nat := 4983230072969 + 3 ^ 40 * 2287240 * 2
def baseEnd_2287240 : Nat := 130494832465526266297909

theorem tailTrace_2287240 : CollatzResearch.WordTrace tailWord_2287240 prefixEnd_2287240 130494832465526266297909 := by
  unfold tailWord_2287240
  simp only [CollatzResearch.WordTrace]
  refine ⟨41711248116863792168753587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55614997489151722891671449 41711248116863792168753587)
  ·
    refine ⟨62566872175295688253130381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41711248116863792168753587 62566872175295688253130381)
    ·
      refine ⟨23462577065735883094923893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62566872175295688253130381 23462577065735883094923893)
      ·
        refine ⟨2199616599912739040149115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23462577065735883094923893 2199616599912739040149115)
        ·
          refine ⟨3299424899869108560223673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2199616599912739040149115 3299424899869108560223673)
          ·
            refine ⟨2474568674901831420167755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3299424899869108560223673 2474568674901831420167755)
            ·
              refine ⟨3711853012352747130251633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2474568674901831420167755 3711853012352747130251633)
              ·
                refine ⟨2783889759264560347688725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3711853012352747130251633 2783889759264560347688725)
                ·
                  refine ⟨130494832465526266297909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2783889759264560347688725 130494832465526266297909)
                  ·
                    rfl

theorem cell23_2287240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 6].length) (baseStart_2287240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287240 prefixEnd_2287240 := by exact prefixLift 2287240
  have htrace : WordTrace (prefixWord ++ tailWord_2287240) baseStart_2287240 baseEnd_2287240 := by
    simpa [prefixWord, tailWord_2287240, baseEnd_2287240] using wordTrace_append hprefix tailTrace_2287240
  have hstable : (prefixWord ++ tailWord_2287240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287240).length < 2 ^ (prefixWord ++ tailWord_2287240).sum := by decide
  have hdescent : baseEnd_2287240 < baseStart_2287240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287279 : List Nat := [1, 1, 2, 1, 2, 4, 3, 9]
def baseStart_2287279 : Nat := 118140960795 + 2287279 * 2 ^ 59
def prefixEnd_2287279 : Nat := 4983230072969 + 3 ^ 40 * 2287279 * 2
def baseEnd_2287279 : Nat := 43499019182787472003463

theorem tailTrace_2287279 : CollatzResearch.WordTrace tailWord_2287279 prefixEnd_2287279 43499019182787472003463 := by
  unfold tailWord_2287279
  simp only [CollatzResearch.WordTrace]
  refine ⟨83423918680586293998176891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55615945787057529332117927 83423918680586293998176891)
  ·
    refine ⟨125135878020879440997265337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83423918680586293998176891 125135878020879440997265337)
    ·
      refine ⟨93851908515659580747949003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125135878020879440997265337 93851908515659580747949003)
      ·
        refine ⟨140777862773489371121923505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93851908515659580747949003 140777862773489371121923505)
        ·
          refine ⟨105583397080117028341442629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140777862773489371121923505 105583397080117028341442629)
          ·
            refine ⟨19796886952521942814020493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105583397080117028341442629 19796886952521942814020493)
            ·
              refine ⟨7423832607195728555257685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19796886952521942814020493 7423832607195728555257685)
              ·
                refine ⟨43499019182787472003463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7423832607195728555257685 43499019182787472003463)
                ·
                  rfl

theorem cell23_2287279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 9].length) (baseStart_2287279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287279 prefixEnd_2287279 := by exact prefixLift 2287279
  have htrace : WordTrace (prefixWord ++ tailWord_2287279) baseStart_2287279 baseEnd_2287279 := by
    simpa [prefixWord, tailWord_2287279, baseEnd_2287279] using wordTrace_append hprefix tailTrace_2287279
  have hstable : (prefixWord ++ tailWord_2287279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287279).length < 2 ^ (prefixWord ++ tailWord_2287279).sum := by decide
  have hdescent : baseEnd_2287279 < baseStart_2287279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287293 : List Nat := [1, 4, 1, 2, 1, 2, 1, 5, 1, 2, 3]
def baseStart_2287293 : Nat := 118140960795 + 2287293 * 2 ^ 59
def prefixEnd_2287293 : Nat := 4983230072969 + 3 ^ 40 * 2287293 * 2
def baseEnd_2287293 : Nat := 1174480706664424689318437

theorem tailTrace_2287293 : CollatzResearch.WordTrace tailWord_2287293 prefixEnd_2287293 1174480706664424689318437 := by
  unfold tailWord_2287293
  simp only [CollatzResearch.WordTrace]
  refine ⟨83424429302535574389186533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55616286201690382926124355 83424429302535574389186533)
  ·
    refine ⟨15642080494225420197972475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83424429302535574389186533 15642080494225420197972475)
    ·
      refine ⟨23463120741338130296958713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15642080494225420197972475 23463120741338130296958713)
      ·
        refine ⟨17597340556003597722719035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23463120741338130296958713 17597340556003597722719035)
        ·
          refine ⟨26396010834005396584078553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17597340556003597722719035 26396010834005396584078553)
          ·
            refine ⟨19797008125504047438058915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26396010834005396584078553 19797008125504047438058915)
            ·
              refine ⟨29695512188256071157088373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19797008125504047438058915 29695512188256071157088373)
              ·
                refine ⟨2783954267649006670977035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29695512188256071157088373 2783954267649006670977035)
                ·
                  refine ⟨4175931401473510006465553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2783954267649006670977035 4175931401473510006465553)
                  ·
                    refine ⟨3131948551105132504849165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4175931401473510006465553 3131948551105132504849165)
                    ·
                      refine ⟨1174480706664424689318437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3131948551105132504849165 1174480706664424689318437)
                      ·
                        rfl

theorem cell23_2287293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_2287293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287293 prefixEnd_2287293 := by exact prefixLift 2287293
  have htrace : WordTrace (prefixWord ++ tailWord_2287293) baseStart_2287293 baseEnd_2287293 := by
    simpa [prefixWord, tailWord_2287293, baseEnd_2287293] using wordTrace_append hprefix tailTrace_2287293
  have hstable : (prefixWord ++ tailWord_2287293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287293).length < 2 ^ (prefixWord ++ tailWord_2287293).sum := by decide
  have hdescent : baseEnd_2287293 < baseStart_2287293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
