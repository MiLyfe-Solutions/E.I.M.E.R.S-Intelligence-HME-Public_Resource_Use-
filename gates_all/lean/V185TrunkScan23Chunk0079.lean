import V185TrunkScan23Chunk0078

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_469189 : List Nat := [1, 3, 1, 1, 1, 1, 7, 1, 2, 1, 4]
def baseStart_469189 : Nat := 118140960795 + 469189 * 2 ^ 59
def prefixEnd_469189 : Nat := 4983230072969 + 3 ^ 40 * 469189 * 2
def baseEnd_469189 : Nat := 240919474802470029579745

theorem tailTrace_469189 : CollatzResearch.WordTrace tailWord_469189 prefixEnd_469189 240919474802470029579745 := by
  unfold tailWord_469189
  simp only [CollatzResearch.WordTrace]
  refine ⟨17112728697215858946746621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11408485798143905964497747 17112728697215858946746621)
  ·
    refine ⟨6417273261455947105029983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17112728697215858946746621 6417273261455947105029983)
    ·
      refine ⟨9625909892183920657544975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6417273261455947105029983 9625909892183920657544975)
      ·
        refine ⟨14438864838275880986317463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9625909892183920657544975 14438864838275880986317463)
        ·
          refine ⟨21658297257413821479476195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14438864838275880986317463 21658297257413821479476195)
          ·
            refine ⟨32487445886120732219214293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21658297257413821479476195 32487445886120732219214293)
            ·
              refine ⟨761424512955954661387835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 32487445886120732219214293 761424512955954661387835)
              ·
                refine ⟨1142136769433931992081753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761424512955954661387835 1142136769433931992081753)
                ·
                  refine ⟨856602577075448994061315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1142136769433931992081753 856602577075448994061315)
                  ·
                    refine ⟨1284903865613173491091973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 856602577075448994061315 1284903865613173491091973)
                    ·
                      refine ⟨240919474802470029579745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1284903865613173491091973 240919474802470029579745)
                      ·
                        rfl

theorem cell23_469189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_469189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469189 prefixEnd_469189 := by exact prefixLift 469189
  have htrace : WordTrace (prefixWord ++ tailWord_469189) baseStart_469189 baseEnd_469189 := by
    simpa [prefixWord, tailWord_469189, baseEnd_469189] using wordTrace_append hprefix tailTrace_469189
  have hstable : (prefixWord ++ tailWord_469189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469189).length < 2 ^ (prefixWord ++ tailWord_469189).sum := by decide
  have hdescent : baseEnd_469189 < baseStart_469189 := by decide
  rcases family_descends (prefixWord ++ tailWord_469189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469209 : List Nat := [1, 2, 1, 2, 3, 1, 2, 4, 2, 2, 3]
def baseStart_469209 : Nat := 118140960795 + 469209 * 2 ^ 59
def prefixEnd_469209 : Nat := 4983230072969 + 3 ^ 40 * 469209 * 2
def baseEnd_469209 : Nat := 240929744415559951329653

theorem tailTrace_469209 : CollatzResearch.WordTrace tailWord_469209 prefixEnd_469209 240929744415559951329653 := by
  unfold tailWord_469209
  simp only [CollatzResearch.WordTrace]
  refine ⟨17113458157143402362474681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11408972104762268241649787 17113458157143402362474681)
  ·
    refine ⟨12835093617857551771856011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17113458157143402362474681 12835093617857551771856011)
    ·
      refine ⟨19252640426786327657784017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12835093617857551771856011 19252640426786327657784017)
      ·
        refine ⟨14439480320089745743338013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19252640426786327657784017 14439480320089745743338013)
        ·
          refine ⟨5414805120033654653751755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14439480320089745743338013 5414805120033654653751755)
          ·
            refine ⟨8122207680050481980627633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5414805120033654653751755 8122207680050481980627633)
            ·
              refine ⟨6091655760037861485470725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8122207680050481980627633 6091655760037861485470725)
              ·
                refine ⟨1142185455007099028525761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6091655760037861485470725 1142185455007099028525761)
                ·
                  refine ⟨856639091255324271394321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1142185455007099028525761 856639091255324271394321)
                  ·
                    refine ⟨642479318441493203545741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 856639091255324271394321 642479318441493203545741)
                    ·
                      refine ⟨240929744415559951329653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 642479318441493203545741 240929744415559951329653)
                      ·
                        rfl

theorem cell23_469209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_469209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469209 prefixEnd_469209 := by exact prefixLift 469209
  have htrace : WordTrace (prefixWord ++ tailWord_469209) baseStart_469209 baseEnd_469209 := by
    simpa [prefixWord, tailWord_469209, baseEnd_469209] using wordTrace_append hprefix tailTrace_469209
  have hstable : (prefixWord ++ tailWord_469209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469209).length < 2 ^ (prefixWord ++ tailWord_469209).sum := by decide
  have hdescent : baseEnd_469209 < baseStart_469209 := by decide
  rcases family_descends (prefixWord ++ tailWord_469209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469216 : List Nat := [2, 1, 1, 3, 1, 3, 1, 6, 1, 4]
def baseStart_469216 : Nat := 118140960795 + 469216 * 2 ^ 59
def prefixEnd_469216 : Nat := 4983230072969 + 3 ^ 40 * 469216 * 2
def baseEnd_469216 : Nat := 80311112926713807980707

theorem tailTrace_469216 : CollatzResearch.WordTrace tailWord_469216 prefixEnd_469216 80311112926713807980707 := by
  unfold tailWord_469216
  simp only [CollatzResearch.WordTrace]
  refine ⟨8556856734059021278989751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11409142312078695038653001 8556856734059021278989751)
  ·
    refine ⟨12835285101088531918484627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8556856734059021278989751 12835285101088531918484627)
    ·
      refine ⟨19252927651632797877726941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12835285101088531918484627 19252927651632797877726941)
      ·
        refine ⟨7219847869362299204147603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19252927651632797877726941 7219847869362299204147603)
        ·
          refine ⟨10829771804043448806221405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7219847869362299204147603 10829771804043448806221405)
          ·
            refine ⟨4061164426516293302333027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10829771804043448806221405 4061164426516293302333027)
            ·
              refine ⟨6091746639774439953499541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4061164426516293302333027 6091746639774439953499541)
              ·
                refine ⟨285550623739426872820291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6091746639774439953499541 285550623739426872820291)
                ·
                  refine ⟨428325935609140309230437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285550623739426872820291 428325935609140309230437)
                  ·
                    refine ⟨80311112926713807980707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 428325935609140309230437 80311112926713807980707)
                    ·
                      rfl

theorem cell23_469216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 1, 4].length) (baseStart_469216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469216 prefixEnd_469216 := by exact prefixLift 469216
  have htrace : WordTrace (prefixWord ++ tailWord_469216) baseStart_469216 baseEnd_469216 := by
    simpa [prefixWord, tailWord_469216, baseEnd_469216] using wordTrace_append hprefix tailTrace_469216
  have hstable : (prefixWord ++ tailWord_469216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469216).length < 2 ^ (prefixWord ++ tailWord_469216).sum := by decide
  have hdescent : baseEnd_469216 < baseStart_469216 := by decide
  rcases family_descends (prefixWord ++ tailWord_469216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469250 : List Nat := [3, 4, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_469250 : Nat := 118140960795 + 469250 * 2 ^ 59
def prefixEnd_469250 : Nat := 4983230072969 + 3 ^ 40 * 469250 * 2
def baseEnd_469250 : Nat := 80316932374131430305655

theorem tailTrace_469250 : CollatzResearch.WordTrace tailWord_469250 prefixEnd_469250 80316932374131430305655 := by
  unfold tailWord_469250
  simp only [CollatzResearch.WordTrace]
  refine ⟨4278738387498716591179301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11409969033329910909811469 4278738387498716591179301)
  ·
    refine ⟨802263447656009360846119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4278738387498716591179301 802263447656009360846119)
    ·
      refine ⟨1203395171484014041269179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 802263447656009360846119 1203395171484014041269179)
      ·
        refine ⟨1805092757226021061903769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1203395171484014041269179 1805092757226021061903769)
        ·
          refine ⟨1353819567919515796427827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1805092757226021061903769 1353819567919515796427827)
          ·
            refine ⟨2030729351879273694641741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353819567919515796427827 2030729351879273694641741)
            ·
              refine ⟨761523506954727635490653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2030729351879273694641741 761523506954727635490653)
              ·
                refine ⟨285571315108022863308995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 761523506954727635490653 285571315108022863308995)
                ·
                  refine ⟨428356972662034294963493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285571315108022863308995 428356972662034294963493)
                  ·
                    refine ⟨80316932374131430305655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 428356972662034294963493 80316932374131430305655)
                    ·
                      rfl

theorem cell23_469250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_469250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469250 prefixEnd_469250 := by exact prefixLift 469250
  have htrace : WordTrace (prefixWord ++ tailWord_469250) baseStart_469250 baseEnd_469250 := by
    simpa [prefixWord, tailWord_469250, baseEnd_469250] using wordTrace_append hprefix tailTrace_469250
  have hstable : (prefixWord ++ tailWord_469250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469250).length < 2 ^ (prefixWord ++ tailWord_469250).sum := by decide
  have hdescent : baseEnd_469250 < baseStart_469250 := by decide
  rcases family_descends (prefixWord ++ tailWord_469250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469259 : List Nat := [1, 1, 1, 1, 5, 2, 1, 5, 1, 5]
def baseStart_469259 : Nat := 118140960795 + 469259 * 2 ^ 59
def prefixEnd_469259 : Nat := 4983230072969 + 3 ^ 40 * 469259 * 2
def baseEnd_469259 : Nat := 80318472816094918568141

theorem tailTrace_469259 : CollatzResearch.WordTrace tailWord_469259 prefixEnd_469259 80318472816094918568141 := by
  unfold tailWord_469259
  simp only [CollatzResearch.WordTrace]
  refine ⟨17115281806962260901794831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11410187871308173934529887 17115281806962260901794831)
  ·
    refine ⟨25672922710443391352692247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17115281806962260901794831 25672922710443391352692247)
    ·
      refine ⟨38509384065665087029038371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25672922710443391352692247 38509384065665087029038371)
      ·
        refine ⟨57764076098497630543557557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38509384065665087029038371 57764076098497630543557557)
        ·
          refine ⟨5415382134234152863458521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57764076098497630543557557 5415382134234152863458521)
          ·
            refine ⟨4061536600675614647593891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5415382134234152863458521 4061536600675614647593891)
            ·
              refine ⟨6092304901013421971390837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4061536600675614647593891 6092304901013421971390837)
              ·
                refine ⟨571153584470008309817891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6092304901013421971390837 571153584470008309817891)
                ·
                  refine ⟨856730376705012464726837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571153584470008309817891 856730376705012464726837)
                  ·
                    refine ⟨80318472816094918568141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 856730376705012464726837 80318472816094918568141)
                    ·
                      rfl

theorem cell23_469259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 5].length) (baseStart_469259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469259 prefixEnd_469259 := by exact prefixLift 469259
  have htrace : WordTrace (prefixWord ++ tailWord_469259) baseStart_469259 baseEnd_469259 := by
    simpa [prefixWord, tailWord_469259, baseEnd_469259] using wordTrace_append hprefix tailTrace_469259
  have hstable : (prefixWord ++ tailWord_469259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469259).length < 2 ^ (prefixWord ++ tailWord_469259).sum := by decide
  have hdescent : baseEnd_469259 < baseStart_469259 := by decide
  rcases family_descends (prefixWord ++ tailWord_469259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469293 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_469293 : Nat := 118140960795 + 469293 * 2 ^ 59
def prefixEnd_469293 : Nat := 4983230072969 + 3 ^ 40 * 469293 * 2
def baseEnd_469293 : Nat := 80324292263512540893089

theorem tailTrace_469293 : CollatzResearch.WordTrace tailWord_469293 prefixEnd_469293 80324292263512540893089 := by
  unfold tailWord_469293
  simp only [CollatzResearch.WordTrace]
  refine ⟨17116521888839084708532533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11411014592559389805688355 17116521888839084708532533)
  ·
    refine ⟨1604673927078664191424925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17116521888839084708532533 1604673927078664191424925)
    ·
      refine ⟨601752722654499071784347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1604673927078664191424925 601752722654499071784347)
      ·
        refine ⟨902629083981748607676521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601752722654499071784347 902629083981748607676521)
        ·
          refine ⟨676971812986311455757391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 902629083981748607676521 676971812986311455757391)
          ·
            refine ⟨1015457719479467183636087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676971812986311455757391 1015457719479467183636087)
            ·
              refine ⟨1523186579219200775454131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015457719479467183636087 1523186579219200775454131)
              ·
                refine ⟨2284779868828801163181197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523186579219200775454131 2284779868828801163181197)
                ·
                  refine ⟨856792450810800436192949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2284779868828801163181197 856792450810800436192949)
                  ·
                    refine ⟨80324292263512540893089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 856792450810800436192949 80324292263512540893089)
                    ·
                      rfl

theorem cell23_469293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_469293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469293 prefixEnd_469293 := by exact prefixLift 469293
  have htrace : WordTrace (prefixWord ++ tailWord_469293) baseStart_469293 baseEnd_469293 := by
    simpa [prefixWord, tailWord_469293, baseEnd_469293] using wordTrace_append hprefix tailTrace_469293
  have hstable : (prefixWord ++ tailWord_469293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469293).length < 2 ^ (prefixWord ++ tailWord_469293).sum := by decide
  have hdescent : baseEnd_469293 < baseStart_469293 := by decide
  rcases family_descends (prefixWord ++ tailWord_469293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469300 : List Nat := [2, 5, 1, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_469300 : Nat := 118140960795 + 469300 * 2 ^ 59
def prefixEnd_469300 : Nat := 4983230072969 + 3 ^ 40 * 469300 * 2
def baseEnd_469300 : Nat := 240976471155119095291735

theorem tailTrace_469300 : CollatzResearch.WordTrace tailWord_469300 prefixEnd_469300 240976471155119095291735 := by
  unfold tailWord_469300
  simp only [CollatzResearch.WordTrace]
  refine ⟨8558388599906862452018677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11411184799875816602691569 8558388599906862452018677)
  ·
    refine ⟨802348931241268354876751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8558388599906862452018677 802348931241268354876751)
    ·
      refine ⟨1203523396861902532315127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 802348931241268354876751 1203523396861902532315127)
      ·
        refine ⟨1805285095292853798472691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1203523396861902532315127 1805285095292853798472691)
        ·
          refine ⟨2707927642939280697709037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1805285095292853798472691 2707927642939280697709037)
          ·
            refine ⟨1015472866102230261640889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2707927642939280697709037 1015472866102230261640889)
            ·
              refine ⟨761604649576672696230667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1015472866102230261640889 761604649576672696230667)
              ·
                refine ⟨1142406974365009044346001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761604649576672696230667 1142406974365009044346001)
                ·
                  refine ⟨856805230773756783259501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1142406974365009044346001 856805230773756783259501)
                  ·
                    refine ⟨321301961540158793722313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 856805230773756783259501 321301961540158793722313)
                    ·
                      refine ⟨240976471155119095291735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 321301961540158793722313 240976471155119095291735)
                      ·
                        rfl

theorem cell23_469300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_469300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469300 prefixEnd_469300 := by exact prefixLift 469300
  have htrace : WordTrace (prefixWord ++ tailWord_469300) baseStart_469300 baseEnd_469300 := by
    simpa [prefixWord, tailWord_469300, baseEnd_469300] using wordTrace_append hprefix tailTrace_469300
  have hstable : (prefixWord ++ tailWord_469300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469300).length < 2 ^ (prefixWord ++ tailWord_469300).sum := by decide
  have hdescent : baseEnd_469300 < baseStart_469300 := by decide
  rcases family_descends (prefixWord ++ tailWord_469300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469449 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 1, 1, 7]
def baseStart_469449 : Nat := 118140960795 + 469449 * 2 ^ 59
def prefixEnd_469449 : Nat := 4983230072969 + 3 ^ 40 * 469449 * 2
def baseEnd_469449 : Nat := 241052979772639012328549

theorem tailTrace_469449 : CollatzResearch.WordTrace tailWord_469449 prefixEnd_469449 241052979772639012328549 := by
  unfold tailWord_469449
  simp only [CollatzResearch.WordTrace]
  refine ⟨17122211676273923351211401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11414807784182615567474267 17122211676273923351211401)
  ·
    refine ⟨12841658757205442513408551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17122211676273923351211401 12841658757205442513408551)
    ·
      refine ⟨19262488135808163770112827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12841658757205442513408551 19262488135808163770112827)
      ·
        refine ⟨28893732203712245655169241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19262488135808163770112827 28893732203712245655169241)
        ·
          refine ⟨21670299152784184241376931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28893732203712245655169241 21670299152784184241376931)
          ·
            refine ⟨32505448729176276362065397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21670299152784184241376931 32505448729176276362065397)
            ·
              refine ⟨3047385818360275908943631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32505448729176276362065397 3047385818360275908943631)
              ·
                refine ⟨4571078727540413863415447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3047385818360275908943631 4571078727540413863415447)
                ·
                  refine ⟨6856618091310620795123171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4571078727540413863415447 6856618091310620795123171)
                  ·
                    refine ⟨10284927136965931192684757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6856618091310620795123171 10284927136965931192684757)
                    ·
                      refine ⟨241052979772639012328549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10284927136965931192684757 241052979772639012328549)
                      ·
                        rfl

theorem cell23_469449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_469449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469449 prefixEnd_469449 := by exact prefixLift 469449
  have htrace : WordTrace (prefixWord ++ tailWord_469449) baseStart_469449 baseEnd_469449 := by
    simpa [prefixWord, tailWord_469449, baseEnd_469449] using wordTrace_append hprefix tailTrace_469449
  have hstable : (prefixWord ++ tailWord_469449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469449).length < 2 ^ (prefixWord ++ tailWord_469449).sum := by decide
  have hdescent : baseEnd_469449 < baseStart_469449 := by decide
  rcases family_descends (prefixWord ++ tailWord_469449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469527 : List Nat := [1, 1, 3, 6, 1, 2, 1, 1, 2, 1, 4]
def baseStart_469527 : Nat := 118140960795 + 469527 * 2 ^ 59
def prefixEnd_469527 : Nat := 4983230072969 + 3 ^ 40 * 469527 * 2
def baseEnd_469527 : Nat := 241093031263689707153191

theorem tailTrace_469527 : CollatzResearch.WordTrace tailWord_469527 prefixEnd_469527 241093031263689707153191 := by
  unfold tailWord_469527
  simp only [CollatzResearch.WordTrace]
  refine ⟨17125056569991342672550835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11416704379994228448367223 17125056569991342672550835)
  ·
    refine ⟨25687584854987014008826253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17125056569991342672550835 25687584854987014008826253)
    ·
      refine ⟨9632844320620130253309845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25687584854987014008826253 9632844320620130253309845)
      ·
        refine ⟨451539577529068605623899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9632844320620130253309845 451539577529068605623899)
        ·
          refine ⟨677309366293602908435849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451539577529068605623899 677309366293602908435849)
          ·
            refine ⟨507982024720202181326887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 677309366293602908435849 507982024720202181326887)
            ·
              refine ⟨761973037080303271990331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507982024720202181326887 761973037080303271990331)
              ·
                refine ⟨1142959555620454907985497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761973037080303271990331 1142959555620454907985497)
                ·
                  refine ⟨857219666715341180989123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1142959555620454907985497 857219666715341180989123)
                  ·
                    refine ⟨1285829500073011771483685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 857219666715341180989123 1285829500073011771483685)
                    ·
                      refine ⟨241093031263689707153191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1285829500073011771483685 241093031263689707153191)
                      ·
                        rfl

theorem cell23_469527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_469527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469527 prefixEnd_469527 := by exact prefixLift 469527
  have htrace : WordTrace (prefixWord ++ tailWord_469527) baseStart_469527 baseEnd_469527 := by
    simpa [prefixWord, tailWord_469527, baseEnd_469527] using wordTrace_append hprefix tailTrace_469527
  have hstable : (prefixWord ++ tailWord_469527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469527).length < 2 ^ (prefixWord ++ tailWord_469527).sum := by decide
  have hdescent : baseEnd_469527 < baseStart_469527 := by decide
  rcases family_descends (prefixWord ++ tailWord_469527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469560 : List Nat := [2, 1, 2, 1, 4, 1, 4, 1, 3, 1, 3]
def baseStart_469560 : Nat := 118140960795 + 469560 * 2 ^ 59
def prefixEnd_469560 : Nat := 4983230072969 + 3 ^ 40 * 469560 * 2
def baseEnd_469560 : Nat := 241109976125288078040539

theorem tailTrace_469560 : CollatzResearch.WordTrace tailWord_469560 prefixEnd_469560 241109976125288078040539 := by
  unfold tailWord_469560
  simp only [CollatzResearch.WordTrace]
  refine ⟨8563130089435894654251067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11417506785914526205668089 8563130089435894654251067)
  ·
    refine ⟨12844695134153841981376601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8563130089435894654251067 12844695134153841981376601)
    ·
      refine ⟨9633521350615381486032451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12844695134153841981376601 9633521350615381486032451)
      ·
        refine ⟨14450282025923072229048677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9633521350615381486032451 14450282025923072229048677)
        ·
          refine ⟨2709427879860576042946627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14450282025923072229048677 2709427879860576042946627)
          ·
            refine ⟨4064141819790864064419941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709427879860576042946627 4064141819790864064419941)
            ·
              refine ⟨762026591210787012078739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4064141819790864064419941 762026591210787012078739)
              ·
                refine ⟨1143039886816180518118109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762026591210787012078739 1143039886816180518118109)
                ·
                  refine ⟨428639957556067694294291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1143039886816180518118109 428639957556067694294291)
                  ·
                    refine ⟨642959936334101541441437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 428639957556067694294291 642959936334101541441437)
                    ·
                      refine ⟨241109976125288078040539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 642959936334101541441437 241109976125288078040539)
                      ·
                        rfl

theorem cell23_469560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 3, 1, 3].length) (baseStart_469560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469560 prefixEnd_469560 := by exact prefixLift 469560
  have htrace : WordTrace (prefixWord ++ tailWord_469560) baseStart_469560 baseEnd_469560 := by
    simpa [prefixWord, tailWord_469560, baseEnd_469560] using wordTrace_append hprefix tailTrace_469560
  have hstable : (prefixWord ++ tailWord_469560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469560).length < 2 ^ (prefixWord ++ tailWord_469560).sum := by decide
  have hdescent : baseEnd_469560 < baseStart_469560 := by decide
  rcases family_descends (prefixWord ++ tailWord_469560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469583 : List Nat := [1, 1, 2, 1, 1, 2, 5, 4, 1, 1, 4]
def baseStart_469583 : Nat := 118140960795 + 469583 * 2 ^ 59
def prefixEnd_469583 : Nat := 4983230072969 + 3 ^ 40 * 469583 * 2
def baseEnd_469583 : Nat := 241121786180341488052933

theorem tailTrace_469583 : CollatzResearch.WordTrace tailWord_469583 prefixEnd_469583 241121786180341488052933 := by
  unfold tailWord_469583
  simp only [CollatzResearch.WordTrace]
  refine ⟨17127099057788464236589403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11418066038525642824392935 17127099057788464236589403)
  ·
    refine ⟨25690648586682696354884105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17127099057788464236589403 25690648586682696354884105)
    ·
      refine ⟨19267986440012022266163079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25690648586682696354884105 19267986440012022266163079)
      ·
        refine ⟨28901979660018033399244619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19267986440012022266163079 28901979660018033399244619)
        ·
          refine ⟨43352969490027050098866929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28901979660018033399244619 43352969490027050098866929)
          ·
            refine ⟨32514727117520287574150197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43352969490027050098866929 32514727117520287574150197)
            ·
              refine ⟨3048255667267526960076581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32514727117520287574150197 3048255667267526960076581)
              ·
                refine ⟨571547937612661305014359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3048255667267526960076581 571547937612661305014359)
                ·
                  refine ⟨857321906418991957521539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571547937612661305014359 857321906418991957521539)
                  ·
                    refine ⟨1285982859628487936282309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 857321906418991957521539 1285982859628487936282309)
                    ·
                      refine ⟨241121786180341488052933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1285982859628487936282309 241121786180341488052933)
                      ·
                        rfl

theorem cell23_469583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 1, 4].length) (baseStart_469583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469583 prefixEnd_469583 := by exact prefixLift 469583
  have htrace : WordTrace (prefixWord ++ tailWord_469583) baseStart_469583 baseEnd_469583 := by
    simpa [prefixWord, tailWord_469583, baseEnd_469583] using wordTrace_append hprefix tailTrace_469583
  have hstable : (prefixWord ++ tailWord_469583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469583).length < 2 ^ (prefixWord ++ tailWord_469583).sum := by decide
  have hdescent : baseEnd_469583 < baseStart_469583 := by decide
  rcases family_descends (prefixWord ++ tailWord_469583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469600 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 5, 2, 2]
def baseStart_469600 : Nat := 118140960795 + 469600 * 2 ^ 59
def prefixEnd_469600 : Nat := 4983230072969 + 3 ^ 40 * 469600 * 2
def baseEnd_469600 : Nat := 241130515351467921540355

theorem tailTrace_469600 : CollatzResearch.WordTrace tailWord_469600 prefixEnd_469600 241130515351467921540355 := by
  unfold tailWord_469600
  simp only [CollatzResearch.WordTrace]
  refine ⟨8563859549363438069979127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11418479399151250759972169 8563859549363438069979127)
  ·
    refine ⟨12845789324045157104968691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8563859549363438069979127 12845789324045157104968691)
    ·
      refine ⟨19268683986067735657453037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12845789324045157104968691 19268683986067735657453037)
      ·
        refine ⟨7225756494775400871544889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19268683986067735657453037 7225756494775400871544889)
        ·
          refine ⟨5419317371081550653658667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7225756494775400871544889 5419317371081550653658667)
          ·
            refine ⟨8128976056622325980488001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5419317371081550653658667 8128976056622325980488001)
            ·
              refine ⟨6096732042466744485366001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8128976056622325980488001 6096732042466744485366001)
              ·
                refine ⟨4572549031850058364024501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6096732042466744485366001 4572549031850058364024501)
                ·
                  refine ⟨428676471735942971627297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4572549031850058364024501 428676471735942971627297)
                  ·
                    refine ⟨321507353801957228720473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 428676471735942971627297 321507353801957228720473)
                    ·
                      refine ⟨241130515351467921540355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 321507353801957228720473 241130515351467921540355)
                      ·
                        rfl

theorem cell23_469600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_469600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469600 prefixEnd_469600 := by exact prefixLift 469600
  have htrace : WordTrace (prefixWord ++ tailWord_469600) baseStart_469600 baseEnd_469600 := by
    simpa [prefixWord, tailWord_469600, baseEnd_469600] using wordTrace_append hprefix tailTrace_469600
  have hstable : (prefixWord ++ tailWord_469600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469600).length < 2 ^ (prefixWord ++ tailWord_469600).sum := by decide
  have hdescent : baseEnd_469600 < baseStart_469600 := by decide
  rcases family_descends (prefixWord ++ tailWord_469600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469603 : List Nat := [1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 5]
def baseStart_469603 : Nat := 118140960795 + 469603 * 2 ^ 59
def prefixEnd_469603 : Nat := 4983230072969 + 3 ^ 40 * 469603 * 2
def baseEnd_469603 : Nat := 241132055793431409802841

theorem tailTrace_469603 : CollatzResearch.WordTrace tailWord_469603 prefixEnd_469603 241132055793431409802841 := by
  unfold tailWord_469603
  simp only [CollatzResearch.WordTrace]
  refine ⟨17127828517716007652317463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11418552345144005101544975 17127828517716007652317463)
  ·
    refine ⟨25691742776574011478476195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17127828517716007652317463 25691742776574011478476195)
    ·
      refine ⟨38537614164861017217714293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25691742776574011478476195 38537614164861017217714293)
      ·
        refine ⟨3612901327955720364160715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38537614164861017217714293 3612901327955720364160715)
        ·
          refine ⟨5419351991933580546241073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3612901327955720364160715 5419351991933580546241073)
          ·
            refine ⟨4064513993950185409680805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5419351991933580546241073 4064513993950185409680805)
            ·
              refine ⟨762096373865659764315151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4064513993950185409680805 762096373865659764315151)
              ·
                refine ⟨1143144560798489646472727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762096373865659764315151 1143144560798489646472727)
                ·
                  refine ⟨1714716841197734469709091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1143144560798489646472727 1714716841197734469709091)
                  ·
                    refine ⟨2572075261796601704563637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1714716841197734469709091 2572075261796601704563637)
                    ·
                      refine ⟨241132055793431409802841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2572075261796601704563637 241132055793431409802841)
                      ·
                        rfl

theorem cell23_469603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_469603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469603 prefixEnd_469603 := by exact prefixLift 469603
  have htrace : WordTrace (prefixWord ++ tailWord_469603) baseStart_469603 baseEnd_469603 := by
    simpa [prefixWord, tailWord_469603, baseEnd_469603] using wordTrace_append hprefix tailTrace_469603
  have hstable : (prefixWord ++ tailWord_469603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469603).length < 2 ^ (prefixWord ++ tailWord_469603).sum := by decide
  have hdescent : baseEnd_469603 < baseStart_469603 := by decide
  rcases family_descends (prefixWord ++ tailWord_469603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469610 : List Nat := [3, 1, 3, 2, 1, 1, 2, 4, 2, 4]
def baseStart_469610 : Nat := 118140960795 + 469610 * 2 ^ 59
def prefixEnd_469610 : Nat := 4983230072969 + 3 ^ 40 * 469610 * 2
def baseEnd_469610 : Nat := 80378550052670960805103

theorem tailTrace_469610 : CollatzResearch.WordTrace tailWord_469610 prefixEnd_469610 80378550052670960805103 := by
  unfold tailWord_469610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4282020957172661961955571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11418722552460431898548189 4282020957172661961955571)
  ·
    refine ⟨6423031435758992942933357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4282020957172661961955571 6423031435758992942933357)
    ·
      refine ⟨2408636788409622353600009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6423031435758992942933357 2408636788409622353600009)
      ·
        refine ⟨1806477591307216765200007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2408636788409622353600009 1806477591307216765200007)
        ·
          refine ⟨2709716386960825147800011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1806477591307216765200007 2709716386960825147800011)
          ·
            refine ⟨4064574580441237721700017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709716386960825147800011 4064574580441237721700017)
            ·
              refine ⟨3048430935330928291275013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4064574580441237721700017 3048430935330928291275013)
              ·
                refine ⟨571580800374549054614065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3048430935330928291275013 571580800374549054614065)
                ·
                  refine ⟨428685600280911790960549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 571580800374549054614065 428685600280911790960549)
                  ·
                    refine ⟨80378550052670960805103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 428685600280911790960549 80378550052670960805103)
                    ·
                      rfl

theorem cell23_469610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_469610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469610 prefixEnd_469610 := by exact prefixLift 469610
  have htrace : WordTrace (prefixWord ++ tailWord_469610) baseStart_469610 baseEnd_469610 := by
    simpa [prefixWord, tailWord_469610, baseEnd_469610] using wordTrace_append hprefix tailTrace_469610
  have hstable : (prefixWord ++ tailWord_469610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469610).length < 2 ^ (prefixWord ++ tailWord_469610).sum := by decide
  have hdescent : baseEnd_469610 < baseStart_469610 := by decide
  rcases family_descends (prefixWord ++ tailWord_469610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469613 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_469613 : Nat := 118140960795 + 469613 * 2 ^ 59
def prefixEnd_469613 : Nat := 4983230072969 + 3 ^ 40 * 469613 * 2
def baseEnd_469613 : Nat := 241137190599976370677795

theorem tailTrace_469613 : CollatzResearch.WordTrace tailWord_469613 prefixEnd_469613 241137190599976370677795 := by
  unfold tailWord_469613
  simp only [CollatzResearch.WordTrace]
  refine ⟨17128193247679779360181493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11418795498453186240120995 17128193247679779360181493)
  ·
    refine ⟨1605768116969979315017015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17128193247679779360181493 1605768116969979315017015)
    ·
      refine ⟨2408652175454968972525523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1605768116969979315017015 2408652175454968972525523)
      ·
        refine ⟨3612978263182453458788285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2408652175454968972525523 3612978263182453458788285)
        ·
          refine ⟨1354866848693420047045607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3612978263182453458788285 1354866848693420047045607)
          ·
            refine ⟨2032300273040130070568411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1354866848693420047045607 2032300273040130070568411)
            ·
              refine ⟨3048450409560195105852617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2032300273040130070568411 3048450409560195105852617)
              ·
                refine ⟨2286337807170146329389463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3048450409560195105852617 2286337807170146329389463)
                ·
                  refine ⟨3429506710755219494084195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2286337807170146329389463 3429506710755219494084195)
                  ·
                    refine ⟨5144260066132829241126293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3429506710755219494084195 5144260066132829241126293)
                    ·
                      refine ⟨241137190599976370677795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5144260066132829241126293 241137190599976370677795)
                      ·
                        rfl

theorem cell23_469613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_469613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469613 prefixEnd_469613 := by exact prefixLift 469613
  have htrace : WordTrace (prefixWord ++ tailWord_469613) baseStart_469613 baseEnd_469613 := by
    simpa [prefixWord, tailWord_469613, baseEnd_469613] using wordTrace_append hprefix tailTrace_469613
  have hstable : (prefixWord ++ tailWord_469613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469613).length < 2 ^ (prefixWord ++ tailWord_469613).sum := by decide
  have hdescent : baseEnd_469613 < baseStart_469613 := by decide
  rcases family_descends (prefixWord ++ tailWord_469613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469637 : List Nat := [1, 3, 1, 1, 4, 4, 1, 2, 1, 2, 3]
def baseStart_469637 : Nat := 118140960795 + 469637 * 2 ^ 59
def prefixEnd_469637 : Nat := 4983230072969 + 3 ^ 40 * 469637 * 2
def baseEnd_469637 : Nat := 241149514135684276777685

theorem tailTrace_469637 : CollatzResearch.WordTrace tailWord_469637 prefixEnd_469637 241149514135684276777685 := by
  unfold tailWord_469637
  simp only [CollatzResearch.WordTrace]
  refine ⟨17129068599592831459055165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11419379066395220972703443 17129068599592831459055165)
  ·
    refine ⟨6423400724847311797145687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17129068599592831459055165 6423400724847311797145687)
    ·
      refine ⟨9635101087270967695718531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6423400724847311797145687 9635101087270967695718531)
      ·
        refine ⟨14452651630906451543577797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9635101087270967695718531 14452651630906451543577797)
        ·
          refine ⟨2709872180794959664420837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14452651630906451543577797 2709872180794959664420837)
          ·
            refine ⟨508101033899054937078907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2709872180794959664420837 508101033899054937078907)
            ·
              refine ⟨762151550848582405618361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508101033899054937078907 762151550848582405618361)
              ·
                refine ⟨571613663136436804213771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 762151550848582405618361 571613663136436804213771)
                ·
                  refine ⟨857420494704655206320657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571613663136436804213771 857420494704655206320657)
                  ·
                    refine ⟨643065371028491404740493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 857420494704655206320657 643065371028491404740493)
                    ·
                      refine ⟨241149514135684276777685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 643065371028491404740493 241149514135684276777685)
                      ·
                        rfl

theorem cell23_469637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 2, 3].length) (baseStart_469637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469637 prefixEnd_469637 := by exact prefixLift 469637
  have htrace : WordTrace (prefixWord ++ tailWord_469637) baseStart_469637 baseEnd_469637 := by
    simpa [prefixWord, tailWord_469637, baseEnd_469637] using wordTrace_append hprefix tailTrace_469637
  have hstable : (prefixWord ++ tailWord_469637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469637).length < 2 ^ (prefixWord ++ tailWord_469637).sum := by decide
  have hdescent : baseEnd_469637 < baseStart_469637 := by decide
  rcases family_descends (prefixWord ++ tailWord_469637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469650 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_469650 : Nat := 118140960795 + 469650 * 2 ^ 59
def prefixEnd_469650 : Nat := 4983230072969 + 3 ^ 40 * 469650 * 2
def baseEnd_469650 : Nat := 241156189384192725915125

theorem tailTrace_469650 : CollatzResearch.WordTrace tailWord_469650 prefixEnd_469650 241156189384192725915125 := by
  unfold tailWord_469650
  simp only [CollatzResearch.WordTrace]
  refine ⟨4282385687136433669819601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11419695165697156452852269 4282385687136433669819601)
  ·
    refine ⟨3211789265352325252364701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4282385687136433669819601 3211789265352325252364701)
    ·
      refine ⟨1204420974507121969636763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3211789265352325252364701 1204420974507121969636763)
      ·
        refine ⟨1806631461760682954455145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1204420974507121969636763 1806631461760682954455145)
        ·
          refine ⟨1354973596320512215841359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1806631461760682954455145 1354973596320512215841359)
          ·
            refine ⟨2032460394480768323762039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1354973596320512215841359 2032460394480768323762039)
            ·
              refine ⟨3048690591721152485643059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2032460394480768323762039 3048690591721152485643059)
              ·
                refine ⟨4573035887581728728464589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3048690591721152485643059 4573035887581728728464589)
                ·
                  refine ⟨1714888457843148273174221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4573035887581728728464589 1714888457843148273174221)
                  ·
                    refine ⟨643083171691180602440333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1714888457843148273174221 643083171691180602440333)
                    ·
                      refine ⟨241156189384192725915125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 643083171691180602440333 241156189384192725915125)
                      ·
                        rfl

theorem cell23_469650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_469650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469650 prefixEnd_469650 := by exact prefixLift 469650
  have htrace : WordTrace (prefixWord ++ tailWord_469650) baseStart_469650 baseEnd_469650 := by
    simpa [prefixWord, tailWord_469650, baseEnd_469650] using wordTrace_append hprefix tailTrace_469650
  have hstable : (prefixWord ++ tailWord_469650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469650).length < 2 ^ (prefixWord ++ tailWord_469650).sum := by decide
  have hdescent : baseEnd_469650 < baseStart_469650 := by decide
  rcases family_descends (prefixWord ++ tailWord_469650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469674 : List Nat := [3, 1, 5, 2, 2, 1, 1, 8]
def baseStart_469674 : Nat := 118140960795 + 469674 * 2 ^ 59
def prefixEnd_469674 : Nat := 4983230072969 + 3 ^ 40 * 469674 * 2
def baseEnd_469674 : Nat := 8932167145181504889445

theorem tailTrace_469674 : CollatzResearch.WordTrace tailWord_469674 prefixEnd_469674 8932167145181504889445 := by
  unfold tailWord_469674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4282604525114696694538019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11420278733639191185434717 4282604525114696694538019)
  ·
    refine ⟨6423906787672045041807029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4282604525114696694538019 6423906787672045041807029)
    ·
      refine ⟨602241261344254222669409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6423906787672045041807029 602241261344254222669409)
      ·
        refine ⟨451680946008190667002057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602241261344254222669409 451680946008190667002057)
        ·
          refine ⟨338760709506143000251543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451680946008190667002057 338760709506143000251543)
          ·
            refine ⟨508141064259214500377315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338760709506143000251543 508141064259214500377315)
            ·
              refine ⟨762211596388821750565973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508141064259214500377315 762211596388821750565973)
              ·
                refine ⟨8932167145181504889445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 762211596388821750565973 8932167145181504889445)
                ·
                  rfl

theorem cell23_469674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 8].length) (baseStart_469674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469674 prefixEnd_469674 := by exact prefixLift 469674
  have htrace : WordTrace (prefixWord ++ tailWord_469674) baseStart_469674 baseEnd_469674 := by
    simpa [prefixWord, tailWord_469674, baseEnd_469674] using wordTrace_append hprefix tailTrace_469674
  have hstable : (prefixWord ++ tailWord_469674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469674).length < 2 ^ (prefixWord ++ tailWord_469674).sum := by decide
  have hdescent : baseEnd_469674 < baseStart_469674 := by decide
  rcases family_descends (prefixWord ++ tailWord_469674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469677 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_469677 : Nat := 118140960795 + 469677 * 2 ^ 59
def prefixEnd_469677 : Nat := 4983230072969 + 3 ^ 40 * 469677 * 2
def baseEnd_469677 : Nat := 241170053361864120277501

theorem tailTrace_469677 : CollatzResearch.WordTrace tailWord_469677 prefixEnd_469677 241170053361864120277501 := by
  unfold tailWord_469677
  simp only [CollatzResearch.WordTrace]
  refine ⟨17130527519447918290511285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11420351679631945527007523 17130527519447918290511285)
  ·
    refine ⟨1605986954948242339735433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17130527519447918290511285 1605986954948242339735433)
    ·
      refine ⟨1204490216211181754801575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1605986954948242339735433 1204490216211181754801575)
      ·
        refine ⟨1806735324316772632202363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1204490216211181754801575 1806735324316772632202363)
        ·
          refine ⟨2710102986475158948303545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1806735324316772632202363 2710102986475158948303545)
          ·
            refine ⟨2032577239856369211227659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2710102986475158948303545 2032577239856369211227659)
            ·
              refine ⟨3048865859784553816841489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2032577239856369211227659 3048865859784553816841489)
              ·
                refine ⟨2286649394838415362631117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3048865859784553816841489 2286649394838415362631117)
                ·
                  refine ⟨857493523064405760986669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2286649394838415362631117 857493523064405760986669)
                  ·
                    refine ⟨321560071149152160370001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 857493523064405760986669 321560071149152160370001)
                    ·
                      refine ⟨241170053361864120277501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 321560071149152160370001 241170053361864120277501)
                      ·
                        rfl

theorem cell23_469677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_469677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469677 prefixEnd_469677 := by exact prefixLift 469677
  have htrace : WordTrace (prefixWord ++ tailWord_469677) baseStart_469677 baseEnd_469677 := by
    simpa [prefixWord, tailWord_469677, baseEnd_469677] using wordTrace_append hprefix tailTrace_469677
  have hstable : (prefixWord ++ tailWord_469677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469677).length < 2 ^ (prefixWord ++ tailWord_469677).sum := by decide
  have hdescent : baseEnd_469677 < baseStart_469677 := by decide
  rcases family_descends (prefixWord ++ tailWord_469677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469683 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 2, 6]
def baseStart_469683 : Nat := 118140960795 + 469683 * 2 ^ 59
def prefixEnd_469683 : Nat := 4983230072969 + 3 ^ 40 * 469683 * 2
def baseEnd_469683 : Nat := 80391044748597032267491

theorem tailTrace_469683 : CollatzResearch.WordTrace tailWord_469683 prefixEnd_469683 80391044748597032267491 := by
  unfold tailWord_469683
  simp only [CollatzResearch.WordTrace]
  refine ⟨17130746357426181315229703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11420497571617454210153135 17130746357426181315229703)
  ·
    refine ⟨25696119536139271972844555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17130746357426181315229703 25696119536139271972844555)
    ·
      refine ⟨38544179304208907959266833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25696119536139271972844555 38544179304208907959266833)
      ·
        refine ⟨28908134478156680969450125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38544179304208907959266833 28908134478156680969450125)
        ·
          refine ⟨10840550429308755363543797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28908134478156680969450125 10840550429308755363543797)
          ·
            refine ⟨1016301602747695815332231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10840550429308755363543797 1016301602747695815332231)
            ·
              refine ⟨1524452404121543722998347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016301602747695815332231 1524452404121543722998347)
              ·
                refine ⟨2286678606182315584497521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1524452404121543722998347 2286678606182315584497521)
                ·
                  refine ⟨1715008954636736688373141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2286678606182315584497521 1715008954636736688373141)
                  ·
                    refine ⟨80391044748597032267491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1715008954636736688373141 80391044748597032267491)
                    ·
                      rfl

theorem cell23_469683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 6].length) (baseStart_469683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469683 prefixEnd_469683 := by exact prefixLift 469683
  have htrace : WordTrace (prefixWord ++ tailWord_469683) baseStart_469683 baseEnd_469683 := by
    simpa [prefixWord, tailWord_469683, baseEnd_469683] using wordTrace_append hprefix tailTrace_469683
  have hstable : (prefixWord ++ tailWord_469683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469683).length < 2 ^ (prefixWord ++ tailWord_469683).sum := by decide
  have hdescent : baseEnd_469683 < baseStart_469683 := by decide
  rcases family_descends (prefixWord ++ tailWord_469683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469741 : List Nat := [1, 5, 1, 2, 1, 1, 5, 1, 2, 2, 2]
def baseStart_469741 : Nat := 118140960795 + 469741 * 2 ^ 59
def prefixEnd_469741 : Nat := 4983230072969 + 3 ^ 40 * 469741 * 2
def baseEnd_469741 : Nat := 241202916123751869877207

theorem tailTrace_469741 : CollatzResearch.WordTrace tailWord_469741 prefixEnd_469741 241202916123751869877207 := by
  unfold tailWord_469741
  simp only [CollatzResearch.WordTrace]
  refine ⟨17132861791216057220841077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11421907860810704813894051 17132861791216057220841077)
  ·
    refine ⟨1606205792926505364453851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17132861791216057220841077 1606205792926505364453851)
    ·
      refine ⟨2409308689389758046680777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1606205792926505364453851 2409308689389758046680777)
      ·
        refine ⟨1806981517042318535010583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2409308689389758046680777 1806981517042318535010583)
        ·
          refine ⟨2710472275563477802515875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1806981517042318535010583 2710472275563477802515875)
          ·
            refine ⟨4065708413345216703773813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710472275563477802515875 4065708413345216703773813)
            ·
              refine ⟨381160163751114065978795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4065708413345216703773813 381160163751114065978795)
              ·
                refine ⟨571740245626671098968193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381160163751114065978795 571740245626671098968193)
                ·
                  refine ⟨428805184220003324226145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 571740245626671098968193 428805184220003324226145)
                  ·
                    refine ⟨321603888165002493169609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 428805184220003324226145 321603888165002493169609)
                    ·
                      refine ⟨241202916123751869877207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 321603888165002493169609 241202916123751869877207)
                      ·
                        rfl

theorem cell23_469741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_469741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469741 prefixEnd_469741 := by exact prefixLift 469741
  have htrace : WordTrace (prefixWord ++ tailWord_469741) baseStart_469741 baseEnd_469741 := by
    simpa [prefixWord, tailWord_469741, baseEnd_469741] using wordTrace_append hprefix tailTrace_469741
  have hstable : (prefixWord ++ tailWord_469741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469741).length < 2 ^ (prefixWord ++ tailWord_469741).sum := by decide
  have hdescent : baseEnd_469741 < baseStart_469741 := by decide
  rcases family_descends (prefixWord ++ tailWord_469741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469743 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 1, 7]
def baseStart_469743 : Nat := 118140960795 + 469743 * 2 ^ 59
def prefixEnd_469743 : Nat := 4983230072969 + 3 ^ 40 * 469743 * 2
def baseEnd_469743 : Nat := 80401314361686954017399

theorem tailTrace_469743 : CollatzResearch.WordTrace tailWord_469743 prefixEnd_469743 80401314361686954017399 := by
  unfold tailWord_469743
  simp only [CollatzResearch.WordTrace]
  refine ⟨17132934737208811562413883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11421956491472541041609255 17132934737208811562413883)
  ·
    refine ⟨25699402105813217343620825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17132934737208811562413883 25699402105813217343620825)
    ·
      refine ⟨19274551579359913007715619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25699402105813217343620825 19274551579359913007715619)
      ·
        refine ⟨28911827369039869511573429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19274551579359913007715619 28911827369039869511573429)
        ·
          refine ⟨2710483815847487766710009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28911827369039869511573429 2710483815847487766710009)
          ·
            refine ⟨2032862861885615825032507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2710483815847487766710009 2032862861885615825032507)
            ·
              refine ⟨3049294292828423737548761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2032862861885615825032507 3049294292828423737548761)
              ·
                refine ⟨2286970719621317803161571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3049294292828423737548761 2286970719621317803161571)
                ·
                  refine ⟨3430456079431976704742357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2286970719621317803161571 3430456079431976704742357)
                  ·
                    refine ⟨80401314361686954017399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3430456079431976704742357 80401314361686954017399)
                    ·
                      rfl

theorem cell23_469743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 7].length) (baseStart_469743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469743 prefixEnd_469743 := by exact prefixLift 469743
  have htrace : WordTrace (prefixWord ++ tailWord_469743) baseStart_469743 baseEnd_469743 := by
    simpa [prefixWord, tailWord_469743, baseEnd_469743] using wordTrace_append hprefix tailTrace_469743
  have hstable : (prefixWord ++ tailWord_469743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469743).length < 2 ^ (prefixWord ++ tailWord_469743).sum := by decide
  have hdescent : baseEnd_469743 < baseStart_469743 := by decide
  rcases family_descends (prefixWord ++ tailWord_469743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469843 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 5]
def baseStart_469843 : Nat := 118140960795 + 469843 * 2 ^ 59
def prefixEnd_469843 : Nat := 4983230072969 + 3 ^ 40 * 469843 * 2
def baseEnd_469843 : Nat := 241255291150510470801737

theorem tailTrace_469843 : CollatzResearch.WordTrace tailWord_469843 prefixEnd_469843 241255291150510470801737 := by
  unfold tailWord_469843
  simp only [CollatzResearch.WordTrace]
  refine ⟨17136582036846528641054183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11424388024564352427369455 17136582036846528641054183)
  ·
    refine ⟨25704873055269792961581275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17136582036846528641054183 25704873055269792961581275)
    ·
      refine ⟨38557309582904689442371913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25704873055269792961581275 38557309582904689442371913)
      ·
        refine ⟨28917982187178517081778935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38557309582904689442371913 28917982187178517081778935)
        ·
          refine ⟨43376973280767775622668403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28917982187178517081778935 43376973280767775622668403)
          ·
            refine ⟨65065459921151663434002605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43376973280767775622668403 65065459921151663434002605)
            ·
              refine ⟨24399547470431873787750977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65065459921151663434002605 24399547470431873787750977)
              ·
                refine ⟨18299660602823905340813233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24399547470431873787750977 18299660602823905340813233)
                ·
                  refine ⟨13724745452117929005609925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18299660602823905340813233 13724745452117929005609925)
                  ·
                    refine ⟨2573389772272111688551861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13724745452117929005609925 2573389772272111688551861)
                    ·
                      refine ⟨241255291150510470801737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2573389772272111688551861 241255291150510470801737)
                      ·
                        rfl

theorem cell23_469843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_469843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469843 prefixEnd_469843 := by exact prefixLift 469843
  have htrace : WordTrace (prefixWord ++ tailWord_469843) baseStart_469843 baseEnd_469843 := by
    simpa [prefixWord, tailWord_469843, baseEnd_469843] using wordTrace_append hprefix tailTrace_469843
  have hstable : (prefixWord ++ tailWord_469843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469843).length < 2 ^ (prefixWord ++ tailWord_469843).sum := by decide
  have hdescent : baseEnd_469843 < baseStart_469843 := by decide
  rcases family_descends (prefixWord ++ tailWord_469843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469850 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 3, 5]
def baseStart_469850 : Nat := 118140960795 + 469850 * 2 ^ 59
def prefixEnd_469850 : Nat := 4983230072969 + 3 ^ 40 * 469850 * 2
def baseEnd_469850 : Nat := 80419628505030647804735

theorem tailTrace_469850 : CollatzResearch.WordTrace tailWord_469850 prefixEnd_469850 80419628505030647804735 := by
  unfold tailWord_469850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4284209336955292209139751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11424558231880779224372669 4284209336955292209139751)
  ·
    refine ⟨6426314005432938313709627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4284209336955292209139751 6426314005432938313709627)
    ·
      refine ⟨9639471008149407470564441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6426314005432938313709627 9639471008149407470564441)
      ·
        refine ⟨7229603256112055602923331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9639471008149407470564441 7229603256112055602923331)
        ·
          refine ⟨10844404884168083404384997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7229603256112055602923331 10844404884168083404384997)
          ·
            refine ⟨2033325915781515638322187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10844404884168083404384997 2033325915781515638322187)
            ·
              refine ⟨3049988873672273457483281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2033325915781515638322187 3049988873672273457483281)
              ·
                refine ⟨2287491655254205093112461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3049988873672273457483281 2287491655254205093112461)
                ·
                  refine ⟨857809370720326909917173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2287491655254205093112461 857809370720326909917173)
                  ·
                    refine ⟨80419628505030647804735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 857809370720326909917173 80419628505030647804735)
                    ·
                      rfl

theorem cell23_469850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_469850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469850 prefixEnd_469850 := by exact prefixLift 469850
  have htrace : WordTrace (prefixWord ++ tailWord_469850) baseStart_469850 baseEnd_469850 := by
    simpa [prefixWord, tailWord_469850, baseEnd_469850] using wordTrace_append hprefix tailTrace_469850
  have hstable : (prefixWord ++ tailWord_469850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469850).length < 2 ^ (prefixWord ++ tailWord_469850).sum := by decide
  have hdescent : baseEnd_469850 < baseStart_469850 := by decide
  rcases family_descends (prefixWord ++ tailWord_469850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469864 : List Nat := [2, 1, 4, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_469864 : Nat := 118140960795 + 469864 * 2 ^ 59
def prefixEnd_469864 : Nat := 4983230072969 + 3 ^ 40 * 469864 * 2
def baseEnd_469864 : Nat := 241266074244254888639141

theorem tailTrace_469864 : CollatzResearch.WordTrace tailWord_469864 prefixEnd_469864 241266074244254888639141 := by
  unfold tailWord_469864
  simp only [CollatzResearch.WordTrace]
  refine ⟨8568673984885224613784323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11424898646513632818379097 8568673984885224613784323)
  ·
    refine ⟨12853010977327836920676485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8568673984885224613784323 12853010977327836920676485)
    ·
      refine ⟨2409939558248969422626841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12853010977327836920676485 2409939558248969422626841)
      ·
        refine ⟨1807454668686727066970131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2409939558248969422626841 1807454668686727066970131)
        ·
          refine ⟨2711182003030090600455197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807454668686727066970131 2711182003030090600455197)
          ·
            refine ⟨1016693251136283975170699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2711182003030090600455197 1016693251136283975170699)
            ·
              refine ⟨1525039876704425962756049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016693251136283975170699 1525039876704425962756049)
              ·
                refine ⟨1143779907528319472067037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1525039876704425962756049 1143779907528319472067037)
                ·
                  refine ⟨428917465323119802025139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1143779907528319472067037 428917465323119802025139)
                  ·
                    refine ⟨643376197984679703037709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 428917465323119802025139 643376197984679703037709)
                    ·
                      refine ⟨241266074244254888639141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 643376197984679703037709 241266074244254888639141)
                      ·
                        rfl

theorem cell23_469864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_469864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469864 prefixEnd_469864 := by exact prefixLift 469864
  have htrace : WordTrace (prefixWord ++ tailWord_469864) baseStart_469864 baseEnd_469864 := by
    simpa [prefixWord, tailWord_469864, baseEnd_469864] using wordTrace_append hprefix tailTrace_469864
  have hstable : (prefixWord ++ tailWord_469864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469864).length < 2 ^ (prefixWord ++ tailWord_469864).sum := by decide
  have hdescent : baseEnd_469864 < baseStart_469864 := by decide
  rcases family_descends (prefixWord ++ tailWord_469864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469874 : List Nat := [3, 2, 1, 2, 1, 1, 5, 1, 2, 3, 2]
def baseStart_469874 : Nat := 118140960795 + 469874 * 2 ^ 59
def prefixEnd_469874 : Nat := 4983230072969 + 3 ^ 40 * 469874 * 2
def baseEnd_469874 : Nat := 241271209050799849514095

theorem tailTrace_469874 : CollatzResearch.WordTrace tailWord_469874 prefixEnd_469874 241271209050799849514095 := by
  unfold tailWord_469874
  simp only [CollatzResearch.WordTrace]
  refine ⟨4284428174933555233858169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11425141799822813956955117 4284428174933555233858169)
  ·
    refine ⟨3213321131200166425393627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4284428174933555233858169 3213321131200166425393627)
    ·
      refine ⟨4819981696800249638090441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3213321131200166425393627 4819981696800249638090441)
      ·
        refine ⟨3614986272600187228567831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4819981696800249638090441 3614986272600187228567831)
        ·
          refine ⟨5422479408900280842851747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3614986272600187228567831 5422479408900280842851747)
          ·
            refine ⟨8133719113350421264277621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5422479408900280842851747 8133719113350421264277621)
            ·
              refine ⟨762536166876601993526027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8133719113350421264277621 762536166876601993526027)
              ·
                refine ⟨1143804250314902990289041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762536166876601993526027 1143804250314902990289041)
                ·
                  refine ⟨857853187736177242716781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1143804250314902990289041 857853187736177242716781)
                  ·
                    refine ⟨321694945401066466018793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 857853187736177242716781 321694945401066466018793)
                    ·
                      refine ⟨241271209050799849514095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 321694945401066466018793 241271209050799849514095)
                      ·
                        rfl

theorem cell23_469874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_469874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469874 prefixEnd_469874 := by exact prefixLift 469874
  have htrace : WordTrace (prefixWord ++ tailWord_469874) baseStart_469874 baseEnd_469874 := by
    simpa [prefixWord, tailWord_469874, baseEnd_469874] using wordTrace_append hprefix tailTrace_469874
  have hstable : (prefixWord ++ tailWord_469874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469874).length < 2 ^ (prefixWord ++ tailWord_469874).sum := by decide
  have hdescent : baseEnd_469874 < baseStart_469874 := by decide
  rcases family_descends (prefixWord ++ tailWord_469874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469881 : List Nat := [1, 2, 1, 3, 2, 4, 2, 3, 1, 1, 3]
def baseStart_469881 : Nat := 118140960795 + 469881 * 2 ^ 59
def prefixEnd_469881 : Nat := 4983230072969 + 3 ^ 40 * 469881 * 2
def baseEnd_469881 : Nat := 241274803415381322126563

theorem tailTrace_469881 : CollatzResearch.WordTrace tailWord_469881 prefixEnd_469881 241274803415381322126563 := by
  unfold tailWord_469881
  simp only [CollatzResearch.WordTrace]
  refine ⟨17137968010708861130937497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11425312007139240753958331 17137968010708861130937497)
  ·
    refine ⟨12853476008031645848203123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17137968010708861130937497 12853476008031645848203123)
    ·
      refine ⟨19280214012047468772304685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12853476008031645848203123 19280214012047468772304685)
      ·
        refine ⟨7230080254517800789614257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19280214012047468772304685 7230080254517800789614257)
        ·
          refine ⟨5422560190888350592210693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7230080254517800789614257 5422560190888350592210693)
          ·
            refine ⟨1016730035791565736039505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5422560190888350592210693 1016730035791565736039505)
            ·
              refine ⟨762547526843674302029629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1016730035791565736039505 762547526843674302029629)
              ·
                refine ⟨285955322566377863261111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 762547526843674302029629 285955322566377863261111)
                ·
                  refine ⟨428932983849566794891667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285955322566377863261111 428932983849566794891667)
                  ·
                    refine ⟨643399475774350192337501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 428932983849566794891667 643399475774350192337501)
                    ·
                      refine ⟨241274803415381322126563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 643399475774350192337501 241274803415381322126563)
                      ·
                        rfl

theorem cell23_469881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 1, 1, 3].length) (baseStart_469881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469881 prefixEnd_469881 := by exact prefixLift 469881
  have htrace : WordTrace (prefixWord ++ tailWord_469881) baseStart_469881 baseEnd_469881 := by
    simpa [prefixWord, tailWord_469881, baseEnd_469881] using wordTrace_append hprefix tailTrace_469881
  have hstable : (prefixWord ++ tailWord_469881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469881).length < 2 ^ (prefixWord ++ tailWord_469881).sum := by decide
  have hdescent : baseEnd_469881 < baseStart_469881 := by decide
  rcases family_descends (prefixWord ++ tailWord_469881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469897 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 4, 4]
def baseStart_469897 : Nat := 118140960795 + 469897 * 2 ^ 59
def prefixEnd_469897 : Nat := 4983230072969 + 3 ^ 40 * 469897 * 2
def baseEnd_469897 : Nat := 80427673035284419842163

theorem tailTrace_469897 : CollatzResearch.WordTrace tailWord_469897 prefixEnd_469897 80427673035284419842163 := by
  unfold tailWord_469897
  simp only [CollatzResearch.WordTrace]
  refine ⟨17138551578650895863519945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11425701052433930575679963 17138551578650895863519945)
  ·
    refine ⟨12853913683988171897639959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17138551578650895863519945 12853913683988171897639959)
    ·
      refine ⟨19280870525982257846459939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12853913683988171897639959 19280870525982257846459939)
      ·
        refine ⟨28921305788973386769689909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19280870525982257846459939 28921305788973386769689909)
        ·
          refine ⟨2711372417716255009658429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28921305788973386769689909 2711372417716255009658429)
          ·
            refine ⟨1016764656643595628621911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2711372417716255009658429 1016764656643595628621911)
            ·
              refine ⟨1525146984965393442932867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016764656643595628621911 1525146984965393442932867)
              ·
                refine ⟨2287720477448090164399301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525146984965393442932867 2287720477448090164399301)
                ·
                  refine ⟨428947589521516905824869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2287720477448090164399301 428947589521516905824869)
                  ·
                    refine ⟨80427673035284419842163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 428947589521516905824869 80427673035284419842163)
                    ·
                      rfl

theorem cell23_469897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 4].length) (baseStart_469897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469897 prefixEnd_469897 := by exact prefixLift 469897
  have htrace : WordTrace (prefixWord ++ tailWord_469897) baseStart_469897 baseEnd_469897 := by
    simpa [prefixWord, tailWord_469897, baseEnd_469897] using wordTrace_append hprefix tailTrace_469897
  have hstable : (prefixWord ++ tailWord_469897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469897).length < 2 ^ (prefixWord ++ tailWord_469897).sum := by decide
  have hdescent : baseEnd_469897 < baseStart_469897 := by decide
  rcases family_descends (prefixWord ++ tailWord_469897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469900 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 3, 2, 4]
def baseStart_469900 : Nat := 118140960795 + 469900 * 2 ^ 59
def prefixEnd_469900 : Nat := 4983230072969 + 3 ^ 40 * 469900 * 2
def baseEnd_469900 : Nat := 241284559547816747788975

theorem tailTrace_469900 : CollatzResearch.WordTrace tailWord_469900 prefixEnd_469900 241284559547816747788975 := by
  unfold tailWord_469900
  simp only [CollatzResearch.WordTrace]
  refine ⟨8569330498820013687939577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11425773998426684917252769 8569330498820013687939577)
  ·
    refine ⟨6426997874115010265954683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8569330498820013687939577 6426997874115010265954683)
    ·
      refine ⟨9640496811172515398932025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6426997874115010265954683 9640496811172515398932025)
      ·
        refine ⟨7230372608379386549199019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9640496811172515398932025 7230372608379386549199019)
        ·
          refine ⟨10845558912569079823798529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7230372608379386549199019 10845558912569079823798529)
          ·
            refine ⟨8134169184426809867848897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10845558912569079823798529 8134169184426809867848897)
            ·
              refine ⟨6100626888320107400886673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8134169184426809867848897 6100626888320107400886673)
              ·
                refine ⟨4575470166240080550665005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6100626888320107400886673 4575470166240080550665005)
                ·
                  refine ⟨1715801312340030206499377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4575470166240080550665005 1715801312340030206499377)
                  ·
                    refine ⟨1286850984255022654874533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1715801312340030206499377 1286850984255022654874533)
                    ·
                      refine ⟨241284559547816747788975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1286850984255022654874533 241284559547816747788975)
                      ·
                        rfl

theorem cell23_469900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_469900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469900 prefixEnd_469900 := by exact prefixLift 469900
  have htrace : WordTrace (prefixWord ++ tailWord_469900) baseStart_469900 baseEnd_469900 := by
    simpa [prefixWord, tailWord_469900, baseEnd_469900] using wordTrace_append hprefix tailTrace_469900
  have hstable : (prefixWord ++ tailWord_469900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469900).length < 2 ^ (prefixWord ++ tailWord_469900).sum := by decide
  have hdescent : baseEnd_469900 < baseStart_469900 := by decide
  rcases family_descends (prefixWord ++ tailWord_469900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469914 : List Nat := [3, 1, 1, 4, 3, 2, 1, 1, 1, 6]
def baseStart_469914 : Nat := 118140960795 + 469914 * 2 ^ 59
def prefixEnd_469914 : Nat := 4983230072969 + 3 ^ 40 * 469914 * 2
def baseEnd_469914 : Nat := 80430582758993231004637

theorem tailTrace_469914 : CollatzResearch.WordTrace tailWord_469914 prefixEnd_469914 80430582758993231004637 := by
  unfold tailWord_469914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4284792904897326941722199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11426114413059538511259197 4284792904897326941722199)
  ·
    refine ⟨6427189357345990412583299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4284792904897326941722199 6427189357345990412583299)
    ·
      refine ⟨9640784036018985618874949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6427189357345990412583299 9640784036018985618874949)
      ·
        refine ⟨1807647006753559803539053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9640784036018985618874949 1807647006753559803539053)
        ·
          refine ⟨677867627532584926327145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1807647006753559803539053 677867627532584926327145)
          ·
            refine ⟨508400720649438694745359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 677867627532584926327145 508400720649438694745359)
            ·
              refine ⟨762601080974158042118039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508400720649438694745359 762601080974158042118039)
              ·
                refine ⟨1143901621461237063177059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762601080974158042118039 1143901621461237063177059)
                ·
                  refine ⟨1715852432191855594765589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1143901621461237063177059 1715852432191855594765589)
                  ·
                    refine ⟨80430582758993231004637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1715852432191855594765589 80430582758993231004637)
                    ·
                      rfl

theorem cell23_469914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_469914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469914 prefixEnd_469914 := by exact prefixLift 469914
  have htrace : WordTrace (prefixWord ++ tailWord_469914) baseStart_469914 baseEnd_469914 := by
    simpa [prefixWord, tailWord_469914, baseEnd_469914] using wordTrace_append hprefix tailTrace_469914
  have hstable : (prefixWord ++ tailWord_469914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469914).length < 2 ^ (prefixWord ++ tailWord_469914).sum := by decide
  have hdescent : baseEnd_469914 < baseStart_469914 := by decide
  rcases family_descends (prefixWord ++ tailWord_469914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469921 : List Nat := [1, 2, 3, 4, 1, 1, 2, 2, 3, 2, 2]
def baseStart_469921 : Nat := 118140960795 + 469921 * 2 ^ 59
def prefixEnd_469921 : Nat := 4983230072969 + 3 ^ 40 * 469921 * 2
def baseEnd_469921 : Nat := 241295342641561165626379

theorem tailTrace_469921 : CollatzResearch.WordTrace tailWord_469921 prefixEnd_469921 241295342641561165626379 := by
  unfold tailWord_469921
  simp only [CollatzResearch.WordTrace]
  refine ⟨17139426930563947962393617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11426284620375965308262411 17139426930563947962393617)
  ·
    refine ⟨12854570197922960971795213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17139426930563947962393617 12854570197922960971795213)
    ·
      refine ⟨4820463824221110364423205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12854570197922960971795213 4820463824221110364423205)
      ·
        refine ⟨903836967041458193329351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4820463824221110364423205 903836967041458193329351)
        ·
          refine ⟨1355755450562187289994027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903836967041458193329351 1355755450562187289994027)
          ·
            refine ⟨2033633175843280934991041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355755450562187289994027 2033633175843280934991041)
            ·
              refine ⟨1525224881882460701243281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2033633175843280934991041 1525224881882460701243281)
              ·
                refine ⟨1143918661411845525932461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1525224881882460701243281 1143918661411845525932461)
                ·
                  refine ⟨428969498029442072224673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1143918661411845525932461 428969498029442072224673)
                  ·
                    refine ⟨321727123522081554168505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 428969498029442072224673 321727123522081554168505)
                    ·
                      refine ⟨241295342641561165626379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 321727123522081554168505 241295342641561165626379)
                      ·
                        rfl

theorem cell23_469921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_469921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469921 prefixEnd_469921 := by exact prefixLift 469921
  have htrace : WordTrace (prefixWord ++ tailWord_469921) baseStart_469921 baseEnd_469921 := by
    simpa [prefixWord, tailWord_469921, baseEnd_469921] using wordTrace_append hprefix tailTrace_469921
  have hstable : (prefixWord ++ tailWord_469921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469921).length < 2 ^ (prefixWord ++ tailWord_469921).sum := by decide
  have hdescent : baseEnd_469921 < baseStart_469921 := by decide
  rcases family_descends (prefixWord ++ tailWord_469921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469924 : List Nat := [2, 3, 1, 2, 1, 2, 4, 2, 1, 2, 3]
def baseStart_469924 : Nat := 118140960795 + 469924 * 2 ^ 59
def prefixEnd_469924 : Nat := 4983230072969 + 3 ^ 40 * 469924 * 2
def baseEnd_469924 : Nat := 241296883083524653888865

theorem tailTrace_469924 : CollatzResearch.WordTrace tailWord_469924 prefixEnd_469924 241296883083524653888865 := by
  unfold tailWord_469924
  simp only [CollatzResearch.WordTrace]
  refine ⟨8569768174776539737376413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11426357566368719649835217 8569768174776539737376413)
  ·
    refine ⟨3213663065541202401516155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8569768174776539737376413 3213663065541202401516155)
    ·
      refine ⟨4820494598311803602274233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3213663065541202401516155 4820494598311803602274233)
      ·
        refine ⟨3615370948733852701705675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4820494598311803602274233 3615370948733852701705675)
        ·
          refine ⟨5423056423100779052558513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3615370948733852701705675 5423056423100779052558513)
          ·
            refine ⟨4067292317325584289418885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5423056423100779052558513 4067292317325584289418885)
            ·
              refine ⟨762617309498547054266041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4067292317325584289418885 762617309498547054266041)
              ·
                refine ⟨571962982123910290699531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 762617309498547054266041 571962982123910290699531)
                ·
                  refine ⟨857944473185865436049297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571962982123910290699531 857944473185865436049297)
                  ·
                    refine ⟨643458354889399077036973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 857944473185865436049297 643458354889399077036973)
                    ·
                      refine ⟨241296883083524653888865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 643458354889399077036973 241296883083524653888865)
                      ·
                        rfl

theorem cell23_469924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_469924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469924 prefixEnd_469924 := by exact prefixLift 469924
  have htrace : WordTrace (prefixWord ++ tailWord_469924) baseStart_469924 baseEnd_469924 := by
    simpa [prefixWord, tailWord_469924, baseEnd_469924] using wordTrace_append hprefix tailTrace_469924
  have hstable : (prefixWord ++ tailWord_469924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469924).length < 2 ^ (prefixWord ++ tailWord_469924).sum := by decide
  have hdescent : baseEnd_469924 < baseStart_469924 := by decide
  rcases family_descends (prefixWord ++ tailWord_469924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469927 : List Nat := [1, 1, 6, 1, 3, 1, 1, 9]
def baseStart_469927 : Nat := 118140960795 + 469927 * 2 ^ 59
def prefixEnd_469927 : Nat := 4983230072969 + 3 ^ 40 * 469927 * 2
def baseEnd_469927 : Nat := 8936978649092153413013

theorem tailTrace_469927 : CollatzResearch.WordTrace tailWord_469927 prefixEnd_469927 8936978649092153413013 := by
  unfold tailWord_469927
  simp only [CollatzResearch.WordTrace]
  refine ⟨17139645768542210987112035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11426430512361473991408023 17139645768542210987112035)
  ·
    refine ⟨25709468652813316480668053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17139645768542210987112035 25709468652813316480668053)
    ·
      refine ⟨1205131343100624210031315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25709468652813316480668053 1205131343100624210031315)
      ·
        refine ⟨1807697014650936315046973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1205131343100624210031315 1807697014650936315046973)
        ·
          refine ⟨677886380494101118142615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1807697014650936315046973 677886380494101118142615)
          ·
            refine ⟨1016829570741151677213923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677886380494101118142615 1016829570741151677213923)
            ·
              refine ⟨1525244356111727515820885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016829570741151677213923 1525244356111727515820885)
              ·
                refine ⟨8936978649092153413013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1525244356111727515820885 8936978649092153413013)
                ·
                  rfl

theorem cell23_469927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 9].length) (baseStart_469927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469927 prefixEnd_469927 := by exact prefixLift 469927
  have htrace : WordTrace (prefixWord ++ tailWord_469927) baseStart_469927 baseEnd_469927 := by
    simpa [prefixWord, tailWord_469927, baseEnd_469927] using wordTrace_append hprefix tailTrace_469927
  have hstable : (prefixWord ++ tailWord_469927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469927).length < 2 ^ (prefixWord ++ tailWord_469927).sum := by decide
  have hdescent : baseEnd_469927 < baseStart_469927 := by decide
  rcases family_descends (prefixWord ++ tailWord_469927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469964 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 3, 3, 2]
def baseStart_469964 : Nat := 118140960795 + 469964 * 2 ^ 59
def prefixEnd_469964 : Nat := 4983230072969 + 3 ^ 40 * 469964 * 2
def baseEnd_469964 : Nat := 241317422309704497388681

theorem tailTrace_469964 : CollatzResearch.WordTrace tailWord_469964 prefixEnd_469964 241317422309704497388681 := by
  unfold tailWord_469964
  simp only [CollatzResearch.WordTrace]
  refine ⟨8570497634704083153104473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11427330179605444204139297 8570497634704083153104473)
  ·
    refine ⟨6427873226028062364828355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8570497634704083153104473 6427873226028062364828355)
    ·
      refine ⟨9641809839042093547242533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6427873226028062364828355 9641809839042093547242533)
      ·
        refine ⟨1807839344820392540107975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9641809839042093547242533 1807839344820392540107975)
        ·
          refine ⟨2711759017230588810161963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807839344820392540107975 2711759017230588810161963)
          ·
            refine ⟨4067638525845883215242945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2711759017230588810161963 4067638525845883215242945)
            ·
              refine ⟨3050728894384412411432209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4067638525845883215242945 3050728894384412411432209)
              ·
                refine ⟨2288046670788309308574157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3050728894384412411432209 2288046670788309308574157)
                ·
                  refine ⟨858017501545615990715309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2288046670788309308574157 858017501545615990715309)
                  ·
                    refine ⟨321756563079605996518241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 858017501545615990715309 321756563079605996518241)
                    ·
                      refine ⟨241317422309704497388681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 321756563079605996518241 241317422309704497388681)
                      ·
                        rfl

theorem cell23_469964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_469964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469964 prefixEnd_469964 := by exact prefixLift 469964
  have htrace : WordTrace (prefixWord ++ tailWord_469964) baseStart_469964 baseEnd_469964 := by
    simpa [prefixWord, tailWord_469964, baseEnd_469964] using wordTrace_append hprefix tailTrace_469964
  have hstable : (prefixWord ++ tailWord_469964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469964).length < 2 ^ (prefixWord ++ tailWord_469964).sum := by decide
  have hdescent : baseEnd_469964 < baseStart_469964 := by decide
  rcases family_descends (prefixWord ++ tailWord_469964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469965 : List Nat := [1, 6, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_469965 : Nat := 118140960795 + 469965 * 2 ^ 59
def prefixEnd_469965 : Nat := 4983230072969 + 3 ^ 40 * 469965 * 2
def baseEnd_469965 : Nat := 80439311930119664492059

theorem tailTrace_469965 : CollatzResearch.WordTrace tailWord_469965 prefixEnd_469965 80439311930119664492059 := by
  unfold tailWord_469965
  simp only [CollatzResearch.WordTrace]
  refine ⟨17141031742404543476995349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11427354494936362317996899 17141031742404543476995349)
  ·
    refine ⟨803485862925212975484157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17141031742404543476995349 803485862925212975484157)
    ·
      refine ⟨301307198596954865806559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 803485862925212975484157 301307198596954865806559)
      ·
        refine ⟨451960797895432298709839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301307198596954865806559 451960797895432298709839)
        ·
          refine ⟨677941196843148448064759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451960797895432298709839 677941196843148448064759)
          ·
            refine ⟨1016911795264722672097139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677941196843148448064759 1016911795264722672097139)
            ·
              refine ⟨1525367692897084008145709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016911795264722672097139 1525367692897084008145709)
              ·
                refine ⟨572012884836406503054641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1525367692897084008145709 572012884836406503054641)
                ·
                  refine ⟨429009663627304877290981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572012884836406503054641 429009663627304877290981)
                  ·
                    refine ⟨80439311930119664492059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 429009663627304877290981 80439311930119664492059)
                    ·
                      rfl

theorem cell23_469965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_469965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469965 prefixEnd_469965 := by exact prefixLift 469965
  have htrace : WordTrace (prefixWord ++ tailWord_469965) baseStart_469965 baseEnd_469965 := by
    simpa [prefixWord, tailWord_469965, baseEnd_469965] using wordTrace_append hprefix tailTrace_469965
  have hstable : (prefixWord ++ tailWord_469965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469965).length < 2 ^ (prefixWord ++ tailWord_469965).sum := by decide
  have hdescent : baseEnd_469965 < baseStart_469965 := by decide
  rcases family_descends (prefixWord ++ tailWord_469965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469981 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_469981 : Nat := 118140960795 + 469981 * 2 ^ 59
def prefixEnd_469981 : Nat := 4983230072969 + 3 ^ 40 * 469981 * 2
def baseEnd_469981 : Nat := 241326151480830930876103

theorem tailTrace_469981 : CollatzResearch.WordTrace tailWord_469981 prefixEnd_469981 241326151480830930876103 := by
  unfold tailWord_469981
  simp only [CollatzResearch.WordTrace]
  refine ⟨17141615310346578209577797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11427743540231052139718531 17141615310346578209577797)
  ·
    refine ⟨3214052870689983414295837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17141615310346578209577797 3214052870689983414295837)
    ·
      refine ⟨1205269826508743780360939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3214052870689983414295837 1205269826508743780360939)
      ·
        refine ⟨1807904739763115670541409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1205269826508743780360939 1807904739763115670541409)
        ·
          refine ⟨1355928554822336752906057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1807904739763115670541409 1355928554822336752906057)
          ·
            refine ⟨1016946416116752564679543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1355928554822336752906057 1016946416116752564679543)
            ·
              refine ⟨1525419624175128847019315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016946416116752564679543 1525419624175128847019315)
              ·
                refine ⟨2288129436262693270528973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525419624175128847019315 2288129436262693270528973)
                ·
                  refine ⟨858048538598509976448365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2288129436262693270528973 858048538598509976448365)
                  ·
                    refine ⟨321768201974441241168137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 858048538598509976448365 321768201974441241168137)
                    ·
                      refine ⟨241326151480830930876103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 321768201974441241168137 241326151480830930876103)
                      ·
                        rfl

theorem cell23_469981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_469981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469981 prefixEnd_469981 := by exact prefixLift 469981
  have htrace : WordTrace (prefixWord ++ tailWord_469981) baseStart_469981 baseEnd_469981 := by
    simpa [prefixWord, tailWord_469981, baseEnd_469981] using wordTrace_append hprefix tailTrace_469981
  have hstable : (prefixWord ++ tailWord_469981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469981).length < 2 ^ (prefixWord ++ tailWord_469981).sum := by decide
  have hdescent : baseEnd_469981 < baseStart_469981 := by decide
  rcases family_descends (prefixWord ++ tailWord_469981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469994 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 3, 4, 2]
def baseStart_469994 : Nat := 118140960795 + 469994 * 2 ^ 59
def prefixEnd_469994 : Nat := 4983230072969 + 3 ^ 40 * 469994 * 2
def baseEnd_469994 : Nat := 241332826729339380013543

theorem tailTrace_469994 : CollatzResearch.WordTrace tailWord_469994 prefixEnd_469994 241332826729339380013543 := by
  unfold tailWord_469994
  simp only [CollatzResearch.WordTrace]
  refine ⟨4285522364824870357450259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11428059639532987619867357 4285522364824870357450259)
  ·
    refine ⟨6428283547237305536175389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4285522364824870357450259 6428283547237305536175389)
    ·
      refine ⟨2410606330213989576065771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6428283547237305536175389 2410606330213989576065771)
      ·
        refine ⟨3615909495320984364098657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2410606330213989576065771 3615909495320984364098657)
        ·
          refine ⟨2711932121490738273073993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3615909495320984364098657 2711932121490738273073993)
          ·
            refine ⟨2033949091118053704805495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2711932121490738273073993 2033949091118053704805495)
            ·
              refine ⟨3050923636677080557208243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2033949091118053704805495 3050923636677080557208243)
              ·
                refine ⟨4576385455015620835812365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3050923636677080557208243 4576385455015620835812365)
                ·
                  refine ⟨1716144545630857813429637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4576385455015620835812365 1716144545630857813429637)
                  ·
                    refine ⟨321777102305785840018057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1716144545630857813429637 321777102305785840018057)
                    ·
                      refine ⟨241332826729339380013543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 321777102305785840018057 241332826729339380013543)
                      ·
                        rfl

theorem cell23_469994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_469994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469994 prefixEnd_469994 := by exact prefixLift 469994
  have htrace : WordTrace (prefixWord ++ tailWord_469994) baseStart_469994 baseEnd_469994 := by
    simpa [prefixWord, tailWord_469994, baseEnd_469994] using wordTrace_append hprefix tailTrace_469994
  have hstable : (prefixWord ++ tailWord_469994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469994).length < 2 ^ (prefixWord ++ tailWord_469994).sum := by decide
  have hdescent : baseEnd_469994 < baseStart_469994 := by decide
  rcases family_descends (prefixWord ++ tailWord_469994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470005 : List Nat := [1, 3, 5, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_470005 : Nat := 118140960795 + 470005 * 2 ^ 59
def prefixEnd_470005 : Nat := 4983230072969 + 3 ^ 40 * 470005 * 2
def baseEnd_470005 : Nat := 241338475016538836975993

theorem tailTrace_470005 : CollatzResearch.WordTrace tailWord_470005 prefixEnd_470005 241338475016538836975993 := by
  unfold tailWord_470005
  simp only [CollatzResearch.WordTrace]
  refine ⟨17142490662259630308451469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11428327108173086872300979 17142490662259630308451469)
  ·
    refine ⟨6428433998347361365669301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17142490662259630308451469 6428433998347361365669301)
    ·
      refine ⟨602665687345065128031497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6428433998347361365669301 602665687345065128031497)
      ·
        refine ⟨451999265508798846023623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602665687345065128031497 451999265508798846023623)
        ·
          refine ⟨677998898263198269035435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451999265508798846023623 677998898263198269035435)
          ·
            refine ⟨1016998347394797403553153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677998898263198269035435 1016998347394797403553153)
            ·
              refine ⟨762748760546098052664865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1016998347394797403553153 762748760546098052664865)
              ·
                refine ⟨572061570409573539498649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 762748760546098052664865 572061570409573539498649)
                ·
                  refine ⟨429046177807180154623987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572061570409573539498649 429046177807180154623987)
                  ·
                    refine ⟨643569266710770231935981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 429046177807180154623987 643569266710770231935981)
                    ·
                      refine ⟨241338475016538836975993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 643569266710770231935981 241338475016538836975993)
                      ·
                        rfl

theorem cell23_470005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_470005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470005 prefixEnd_470005 := by exact prefixLift 470005
  have htrace : WordTrace (prefixWord ++ tailWord_470005) baseStart_470005 baseEnd_470005 := by
    simpa [prefixWord, tailWord_470005, baseEnd_470005] using wordTrace_append hprefix tailTrace_470005
  have hstable : (prefixWord ++ tailWord_470005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470005).length < 2 ^ (prefixWord ++ tailWord_470005).sum := by decide
  have hdescent : baseEnd_470005 < baseStart_470005 := by decide
  rcases family_descends (prefixWord ++ tailWord_470005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470010 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7]
def baseStart_470010 : Nat := 118140960795 + 470010 * 2 ^ 59
def prefixEnd_470010 : Nat := 4983230072969 + 3 ^ 40 * 470010 * 2
def baseEnd_470010 : Nat := 241341042419811317413469

theorem tailTrace_470010 : CollatzResearch.WordTrace tailWord_470010 prefixEnd_470010 241341042419811317413469 := by
  unfold tailWord_470010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4285668256810379040595871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11428448684827677441588989 4285668256810379040595871)
  ·
    refine ⟨6428502385215568560893807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4285668256810379040595871 6428502385215568560893807)
    ·
      refine ⟨9642753577823352841340711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6428502385215568560893807 9642753577823352841340711)
      ·
        refine ⟨14464130366735029262011067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9642753577823352841340711 14464130366735029262011067)
        ·
          refine ⟨21696195550102543893016601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14464130366735029262011067 21696195550102543893016601)
          ·
            refine ⟨16272146662576907919762451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21696195550102543893016601 16272146662576907919762451)
            ·
              refine ⟨24408219993865361879643677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16272146662576907919762451 24408219993865361879643677)
              ·
                refine ⟨9153082497699510704866379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24408219993865361879643677 9153082497699510704866379)
                ·
                  refine ⟨13729623746549266057299569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9153082497699510704866379 13729623746549266057299569)
                  ·
                    refine ⟨10297217809911949542974677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13729623746549266057299569 10297217809911949542974677)
                    ·
                      refine ⟨241341042419811317413469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10297217809911949542974677 241341042419811317413469)
                      ·
                        rfl

theorem cell23_470010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_470010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470010 prefixEnd_470010 := by exact prefixLift 470010
  have htrace : WordTrace (prefixWord ++ tailWord_470010) baseStart_470010 baseEnd_470010 := by
    simpa [prefixWord, tailWord_470010, baseEnd_470010] using wordTrace_append hprefix tailTrace_470010
  have hstable : (prefixWord ++ tailWord_470010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470010).length < 2 ^ (prefixWord ++ tailWord_470010).sum := by decide
  have hdescent : baseEnd_470010 < baseStart_470010 := by decide
  rcases family_descends (prefixWord ++ tailWord_470010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470027 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 3]
def baseStart_470027 : Nat := 118140960795 + 470027 * 2 ^ 59
def prefixEnd_470027 : Nat := 4983230072969 + 3 ^ 40 * 470027 * 2
def baseEnd_470027 : Nat := 241349771590937750900891

theorem tailTrace_470027 : CollatzResearch.WordTrace tailWord_470027 prefixEnd_470027 241349771590937750900891 := by
  unfold tailWord_470027
  simp only [CollatzResearch.WordTrace]
  refine ⟨17143293068179928065752335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11428862045453285377168223 17143293068179928065752335)
  ·
    refine ⟨25714939602269892098628503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17143293068179928065752335 25714939602269892098628503)
    ·
      refine ⟨38572409403404838147942755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25714939602269892098628503 38572409403404838147942755)
      ·
        refine ⟨57858614105107257221914133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38572409403404838147942755 57858614105107257221914133)
        ·
          refine ⟨2712122536176902682277225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57858614105107257221914133 2712122536176902682277225)
          ·
            refine ⟨2034091902132677011707919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2712122536176902682277225 2034091902132677011707919)
            ·
              refine ⟨3051137853199015517561879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034091902132677011707919 3051137853199015517561879)
              ·
                refine ⟨4576706779798523276342819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3051137853199015517561879 4576706779798523276342819)
                ·
                  refine ⟨6865060169697784914514229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4576706779798523276342819 6865060169697784914514229)
                  ·
                    refine ⟨643599390909167335735709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6865060169697784914514229 643599390909167335735709)
                    ·
                      refine ⟨241349771590937750900891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 643599390909167335735709 241349771590937750900891)
                      ·
                        rfl

theorem cell23_470027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 3].length) (baseStart_470027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470027 prefixEnd_470027 := by exact prefixLift 470027
  have htrace : WordTrace (prefixWord ++ tailWord_470027) baseStart_470027 baseEnd_470027 := by
    simpa [prefixWord, tailWord_470027, baseEnd_470027] using wordTrace_append hprefix tailTrace_470027
  have hstable : (prefixWord ++ tailWord_470027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470027).length < 2 ^ (prefixWord ++ tailWord_470027).sum := by decide
  have hdescent : baseEnd_470027 < baseStart_470027 := by decide
  rcases family_descends (prefixWord ++ tailWord_470027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470047 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 1, 7]
def baseStart_470047 : Nat := 118140960795 + 470047 * 2 ^ 59
def prefixEnd_470047 : Nat := 4983230072969 + 3 ^ 40 * 470047 * 2
def baseEnd_470047 : Nat := 80453347068009224216933

theorem tailTrace_470047 : CollatzResearch.WordTrace tailWord_470047 prefixEnd_470047 80453347068009224216933 := by
  unfold tailWord_470047
  simp only [CollatzResearch.WordTrace]
  refine ⟨17144022528107471481480395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11429348352071647654320263 17144022528107471481480395)
  ·
    refine ⟨25716033792161207222220593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17144022528107471481480395 25716033792161207222220593)
    ·
      refine ⟨19287025344120905416665445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25716033792161207222220593 19287025344120905416665445)
      ·
        refine ⟨3616317252022669765624771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19287025344120905416665445 3616317252022669765624771)
        ·
          refine ⟨5424475878034004648437157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3616317252022669765624771 5424475878034004648437157)
          ·
            refine ⟨1017089227131375871581967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5424475878034004648437157 1017089227131375871581967)
            ·
              refine ⟨1525633840697063807372951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017089227131375871581967 1525633840697063807372951)
              ·
                refine ⟨2288450761045595711059427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525633840697063807372951 2288450761045595711059427)
                ·
                  refine ⟨3432676141568393566589141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2288450761045595711059427 3432676141568393566589141)
                  ·
                    refine ⟨80453347068009224216933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3432676141568393566589141 80453347068009224216933)
                    ·
                      rfl

theorem cell23_470047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 7].length) (baseStart_470047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470047 prefixEnd_470047 := by exact prefixLift 470047
  have htrace : WordTrace (prefixWord ++ tailWord_470047) baseStart_470047 baseEnd_470047 := by
    simpa [prefixWord, tailWord_470047, baseEnd_470047] using wordTrace_append hprefix tailTrace_470047
  have hstable : (prefixWord ++ tailWord_470047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470047).length < 2 ^ (prefixWord ++ tailWord_470047).sum := by decide
  have hdescent : baseEnd_470047 < baseStart_470047 := by decide
  rcases family_descends (prefixWord ++ tailWord_470047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470067 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 4]
def baseStart_470067 : Nat := 118140960795 + 470067 * 2 ^ 59
def prefixEnd_470067 : Nat := 4983230072969 + 3 ^ 40 * 470067 * 2
def baseEnd_470067 : Nat := 241370310817117594400707

theorem tailTrace_470067 : CollatzResearch.WordTrace tailWord_470067 prefixEnd_470067 241370310817117594400707 := by
  unfold tailWord_470067
  simp only [CollatzResearch.WordTrace]
  refine ⟨17144751988035014897208455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11429834658690009931472303 17144751988035014897208455)
  ·
    refine ⟨25717127982052522345812683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17144751988035014897208455 25717127982052522345812683)
    ·
      refine ⟨38575691973078783518719025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25717127982052522345812683 38575691973078783518719025)
      ·
        refine ⟨28931768979809087639039269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38575691973078783518719025 28931768979809087639039269)
        ·
          refine ⟨5424706683714203932319863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28931768979809087639039269 5424706683714203932319863)
          ·
            refine ⟨8137060025571305898479795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5424706683714203932319863 8137060025571305898479795)
            ·
              refine ⟨12205590038356958847719693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8137060025571305898479795 12205590038356958847719693)
              ·
                refine ⟨4577096264383859567894885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12205590038356958847719693 4577096264383859567894885)
                ·
                  refine ⟨858205549571973668980291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4577096264383859567894885 858205549571973668980291)
                  ·
                    refine ⟨1287308324357960503470437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 858205549571973668980291 1287308324357960503470437)
                    ·
                      refine ⟨241370310817117594400707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1287308324357960503470437 241370310817117594400707)
                      ·
                        rfl

theorem cell23_470067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 4].length) (baseStart_470067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470067 prefixEnd_470067 := by exact prefixLift 470067
  have htrace : WordTrace (prefixWord ++ tailWord_470067) baseStart_470067 baseEnd_470067 := by
    simpa [prefixWord, tailWord_470067, baseEnd_470067] using wordTrace_append hprefix tailTrace_470067
  have hstable : (prefixWord ++ tailWord_470067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470067).length < 2 ^ (prefixWord ++ tailWord_470067).sum := by decide
  have hdescent : baseEnd_470067 < baseStart_470067 := by decide
  rcases family_descends (prefixWord ++ tailWord_470067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470094 : List Nat := [4, 1, 1, 1, 1, 3, 1, 4, 3, 4]
def baseStart_470094 : Nat := 118140960795 + 470094 * 2 ^ 59
def prefixEnd_470094 : Nat := 4983230072969 + 3 ^ 40 * 470094 * 2
def baseEnd_470094 : Nat := 80461391598262996254361

theorem tailTrace_470094 : CollatzResearch.WordTrace tailWord_470094 prefixEnd_470094 80461391598262996254361 := by
  unfold tailWord_470094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2143217094867149813555167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11430491172624799005627557 2143217094867149813555167)
  ·
    refine ⟨3214825642300724720332751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2143217094867149813555167 3214825642300724720332751)
    ·
      refine ⟨4822238463451087080499127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3214825642300724720332751 4822238463451087080499127)
      ·
        refine ⟨7233357695176630620748691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4822238463451087080499127 7233357695176630620748691)
        ·
          refine ⟨10850036542764945931123037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7233357695176630620748691 10850036542764945931123037)
          ·
            refine ⟨4068763703536854724171139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10850036542764945931123037 4068763703536854724171139)
            ·
              refine ⟨6103145555305282086256709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4068763703536854724171139 6103145555305282086256709)
              ·
                refine ⟨1144339791619740391173133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6103145555305282086256709 1144339791619740391173133)
                ·
                  refine ⟨429127421857402646689925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1144339791619740391173133 429127421857402646689925)
                  ·
                    refine ⟨80461391598262996254361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 429127421857402646689925 80461391598262996254361)
                    ·
                      rfl

theorem cell23_470094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_470094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470094 prefixEnd_470094 := by exact prefixLift 470094
  have htrace : WordTrace (prefixWord ++ tailWord_470094) baseStart_470094 baseEnd_470094 := by
    simpa [prefixWord, tailWord_470094, baseEnd_470094] using wordTrace_append hprefix tailTrace_470094
  have hstable : (prefixWord ++ tailWord_470094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470094).length < 2 ^ (prefixWord ++ tailWord_470094).sum := by decide
  have hdescent : baseEnd_470094 < baseStart_470094 := by decide
  rcases family_descends (prefixWord ++ tailWord_470094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470102 : List Nat := [5, 2, 2, 1, 3, 1, 1, 3, 5]
def baseStart_470102 : Nat := 118140960795 + 470102 * 2 ^ 59
def prefixEnd_470102 : Nat := 4983230072969 + 3 ^ 40 * 470102 * 2
def baseEnd_470102 : Nat := 26820920293336106384783

theorem tailTrace_470102 : CollatzResearch.WordTrace tailWord_470102 prefixEnd_470102 26820920293336106384783 := by
  unfold tailWord_470102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1071626783931763492170785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11430685695272143916488373 1071626783931763492170785)
  ·
    refine ⟨803720087948822619128089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1071626783931763492170785 803720087948822619128089)
    ·
      refine ⟨602790065961616964346067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 803720087948822619128089 602790065961616964346067)
      ·
        refine ⟨904185098942425446519101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602790065961616964346067 904185098942425446519101)
        ·
          refine ⟨339069412103409542444663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 904185098942425446519101 339069412103409542444663)
          ·
            refine ⟨508604118155114313666995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339069412103409542444663 508604118155114313666995)
            ·
              refine ⟨762906177232671470500493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508604118155114313666995 762906177232671470500493)
              ·
                refine ⟨286089816462251801437685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 762906177232671470500493 286089816462251801437685)
                ·
                  refine ⟨26820920293336106384783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 286089816462251801437685 26820920293336106384783)
                  ·
                    rfl

theorem cell23_470102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_470102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470102 prefixEnd_470102 := by exact prefixLift 470102
  have htrace : WordTrace (prefixWord ++ tailWord_470102) baseStart_470102 baseEnd_470102 := by
    simpa [prefixWord, tailWord_470102, baseEnd_470102] using wordTrace_append hprefix tailTrace_470102
  have hstable : (prefixWord ++ tailWord_470102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470102).length < 2 ^ (prefixWord ++ tailWord_470102).sum := by decide
  have hdescent : baseEnd_470102 < baseStart_470102 := by decide
  rcases family_descends (prefixWord ++ tailWord_470102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470104 : List Nat := [2, 1, 2, 2, 1, 3, 2, 3, 2, 2, 3]
def baseStart_470104 : Nat := 118140960795 + 470104 * 2 ^ 59
def prefixEnd_470104 : Nat := 4983230072969 + 3 ^ 40 * 470104 * 2
def baseEnd_470104 : Nat := 241389309601333949638037

theorem tailTrace_470104 : CollatzResearch.WordTrace tailWord_470104 prefixEnd_470104 241389309601333949638037 := by
  unfold tailWord_470104
  simp only [CollatzResearch.WordTrace]
  refine ⟨8573050744450485108152683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11430734325933980144203577 8573050744450485108152683)
  ·
    refine ⟨12859576116675727662229025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8573050744450485108152683 12859576116675727662229025)
    ·
      refine ⟨9644682087506795746671769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12859576116675727662229025 9644682087506795746671769)
      ·
        refine ⟨7233511565630096810003827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9644682087506795746671769 7233511565630096810003827)
        ·
          refine ⟨10850267348445145215005741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7233511565630096810003827 10850267348445145215005741)
          ·
            refine ⟨4068850255666929455627153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10850267348445145215005741 4068850255666929455627153)
            ·
              refine ⟨3051637691750197091720365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4068850255666929455627153 3051637691750197091720365)
              ·
                refine ⟨1144364134406323909395137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3051637691750197091720365 1144364134406323909395137)
                ·
                  refine ⟨858273100804742932046353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1144364134406323909395137 858273100804742932046353)
                  ·
                    refine ⟨643704825603557199034765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 858273100804742932046353 643704825603557199034765)
                    ·
                      refine ⟨241389309601333949638037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 643704825603557199034765 241389309601333949638037)
                      ·
                        rfl

theorem cell23_470104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_470104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470104 prefixEnd_470104 := by exact prefixLift 470104
  have htrace : WordTrace (prefixWord ++ tailWord_470104) baseStart_470104 baseEnd_470104 := by
    simpa [prefixWord, tailWord_470104, baseEnd_470104] using wordTrace_append hprefix tailTrace_470104
  have hstable : (prefixWord ++ tailWord_470104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470104).length < 2 ^ (prefixWord ++ tailWord_470104).sum := by decide
  have hdescent : baseEnd_470104 < baseStart_470104 := by decide
  rcases family_descends (prefixWord ++ tailWord_470104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470128 : List Nat := [2, 1, 1, 1, 5, 1, 5, 2, 1, 4]
def baseStart_470128 : Nat := 118140960795 + 470128 * 2 ^ 59
def prefixEnd_470128 : Nat := 4983230072969 + 3 ^ 40 * 470128 * 2
def baseEnd_470128 : Nat := 80467211045680618579309

theorem tailTrace_470128 : CollatzResearch.WordTrace tailWord_470128 prefixEnd_470128 80467211045680618579309 := by
  unfold tailWord_470128
  simp only [CollatzResearch.WordTrace]
  refine ⟨8573488420407011157589519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11431317893876014876786025 8573488420407011157589519)
  ·
    refine ⟨12860232630610516736384279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8573488420407011157589519 12860232630610516736384279)
    ·
      refine ⟨19290348945915775104576419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12860232630610516736384279 19290348945915775104576419)
      ·
        refine ⟨28935523418873662656864629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19290348945915775104576419 28935523418873662656864629)
        ·
          refine ⟨2712705320519405874081059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28935523418873662656864629 2712705320519405874081059)
          ·
            refine ⟨4069057980779108811121589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2712705320519405874081059 4069057980779108811121589)
            ·
              refine ⟨381474185698041451042649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4069057980779108811121589 381474185698041451042649)
              ·
                refine ⟨286105639273531088281987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381474185698041451042649 286105639273531088281987)
                ·
                  refine ⟨429158458910296632422981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 286105639273531088281987 429158458910296632422981)
                  ·
                    refine ⟨80467211045680618579309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 429158458910296632422981 80467211045680618579309)
                    ·
                      rfl

theorem cell23_470128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 1, 4].length) (baseStart_470128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470128 prefixEnd_470128 := by exact prefixLift 470128
  have htrace : WordTrace (prefixWord ++ tailWord_470128) baseStart_470128 baseEnd_470128 := by
    simpa [prefixWord, tailWord_470128, baseEnd_470128] using wordTrace_append hprefix tailTrace_470128
  have hstable : (prefixWord ++ tailWord_470128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470128).length < 2 ^ (prefixWord ++ tailWord_470128).sum := by decide
  have hdescent : baseEnd_470128 < baseStart_470128 := by decide
  rcases family_descends (prefixWord ++ tailWord_470128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470144 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 3, 5, 2]
def baseStart_470144 : Nat := 118140960795 + 470144 * 2 ^ 59
def prefixEnd_470144 : Nat := 4983230072969 + 3 ^ 40 * 470144 * 2
def baseEnd_470144 : Nat := 241409848827513793137853

theorem tailTrace_470144 : CollatzResearch.WordTrace tailWord_470144 prefixEnd_470144 241409848827513793137853 := by
  unfold tailWord_470144
  simp only [CollatzResearch.WordTrace]
  refine ⟨8573780204378028523880743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11431706939170704698507657 8573780204378028523880743)
  ·
    refine ⟨12860670306567042785821115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8573780204378028523880743 12860670306567042785821115)
    ·
      refine ⟨19291005459850564178731673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12860670306567042785821115 19291005459850564178731673)
      ·
        refine ⟨14468254094887923134048755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19291005459850564178731673 14468254094887923134048755)
        ·
          refine ⟨21702381142331884701073133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14468254094887923134048755 21702381142331884701073133)
          ·
            refine ⟨8138392928374456762902425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21702381142331884701073133 8138392928374456762902425)
            ·
              refine ⟨6103794696280842572176819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8138392928374456762902425 6103794696280842572176819)
              ·
                refine ⟨9155692044421263858265229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6103794696280842572176819 9155692044421263858265229)
                ·
                  refine ⟨3433384516657973946849461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9155692044421263858265229 3433384516657973946849461)
                  ·
                    refine ⟨321879798436685057517137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3433384516657973946849461 321879798436685057517137)
                    ·
                      refine ⟨241409848827513793137853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 321879798436685057517137 241409848827513793137853)
                      ·
                        rfl

theorem cell23_470144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3, 5, 2].length) (baseStart_470144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470144 prefixEnd_470144 := by exact prefixLift 470144
  have htrace : WordTrace (prefixWord ++ tailWord_470144) baseStart_470144 baseEnd_470144 := by
    simpa [prefixWord, tailWord_470144, baseEnd_470144] using wordTrace_append hprefix tailTrace_470144
  have hstable : (prefixWord ++ tailWord_470144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470144).length < 2 ^ (prefixWord ++ tailWord_470144).sum := by decide
  have hdescent : baseEnd_470144 < baseStart_470144 := by decide
  rcases family_descends (prefixWord ++ tailWord_470144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470154 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 3, 5]
def baseStart_470154 : Nat := 118140960795 + 470154 * 2 ^ 59
def prefixEnd_470154 : Nat := 4983230072969 + 3 ^ 40 * 470154 * 2
def baseEnd_470154 : Nat := 80471661211352918004269

theorem tailTrace_470154 : CollatzResearch.WordTrace tailWord_470154 prefixEnd_470154 80471661211352918004269 := by
  unfold tailWord_470154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4286981284679957188906379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11431950092479885837083677 4286981284679957188906379)
  ·
    refine ⟨6430471927019935783359569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4286981284679957188906379 6430471927019935783359569)
    ·
      refine ⟨4822853945264951837519677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6430471927019935783359569 4822853945264951837519677)
      ·
        refine ⟨1808570229474356939069879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4822853945264951837519677 1808570229474356939069879)
        ·
          refine ⟨2712855344211535408604819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1808570229474356939069879 2712855344211535408604819)
          ·
            refine ⟨4069283016317303112907229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2712855344211535408604819 4069283016317303112907229)
            ·
              refine ⟨1525981131118988667340211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4069283016317303112907229 1525981131118988667340211)
              ·
                refine ⟨2288971696678483001010317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525981131118988667340211 2288971696678483001010317)
                ·
                  refine ⟨858364386254431125378869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2288971696678483001010317 858364386254431125378869)
                  ·
                    refine ⟨80471661211352918004269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 858364386254431125378869 80471661211352918004269)
                    ·
                      rfl

theorem cell23_470154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_470154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470154 prefixEnd_470154 := by exact prefixLift 470154
  have htrace : WordTrace (prefixWord ++ tailWord_470154) baseStart_470154 baseEnd_470154 := by
    simpa [prefixWord, tailWord_470154, baseEnd_470154] using wordTrace_append hprefix tailTrace_470154
  have hstable : (prefixWord ++ tailWord_470154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470154).length < 2 ^ (prefixWord ++ tailWord_470154).sum := by decide
  have hdescent : baseEnd_470154 < baseStart_470154 := by decide
  rcases family_descends (prefixWord ++ tailWord_470154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470201 : List Nat := [1, 2, 1, 4, 1, 3, 2, 3, 2, 4]
def baseStart_470201 : Nat := 118140960795 + 470201 * 2 ^ 59
def prefixEnd_470201 : Nat := 4983230072969 + 3 ^ 40 * 470201 * 2
def baseEnd_470201 : Nat := 80479705741606690041697

theorem tailTrace_470201 : CollatzResearch.WordTrace tailWord_470201 prefixEnd_470201 80479705741606690041697 := by
  unfold tailWord_470201
  simp only [CollatzResearch.WordTrace]
  refine ⟨17149639369549555782586457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11433092913033037188390971 17149639369549555782586457)
  ·
    refine ⟨12862229527162166836939843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17149639369549555782586457 12862229527162166836939843)
    ·
      refine ⟨19293344290743250255409765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12862229527162166836939843 19293344290743250255409765)
      ·
        refine ⟨3617502054514359422889331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19293344290743250255409765 3617502054514359422889331)
        ·
          refine ⟨5426253081771539134333997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3617502054514359422889331 5426253081771539134333997)
          ·
            refine ⟨2034844905664327175375249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5426253081771539134333997 2034844905664327175375249)
            ·
              refine ⟨1526133679248245381531437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2034844905664327175375249 1526133679248245381531437)
              ·
                refine ⟨572300129718092018074289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1526133679248245381531437 572300129718092018074289)
                ·
                  refine ⟨429225097288569013555717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572300129718092018074289 429225097288569013555717)
                  ·
                    refine ⟨80479705741606690041697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 429225097288569013555717 80479705741606690041697)
                    ·
                      rfl

theorem cell23_470201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 4].length) (baseStart_470201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470201 prefixEnd_470201 := by exact prefixLift 470201
  have htrace : WordTrace (prefixWord ++ tailWord_470201) baseStart_470201 baseEnd_470201 := by
    simpa [prefixWord, tailWord_470201, baseEnd_470201] using wordTrace_append hprefix tailTrace_470201
  have hstable : (prefixWord ++ tailWord_470201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470201).length < 2 ^ (prefixWord ++ tailWord_470201).sum := by decide
  have hdescent : baseEnd_470201 < baseStart_470201 := by decide
  rcases family_descends (prefixWord ++ tailWord_470201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470212 : List Nat := [2, 3, 3, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_470212 : Nat := 118140960795 + 470212 * 2 ^ 59
def prefixEnd_470212 : Nat := 4983230072969 + 3 ^ 40 * 470212 * 2
def baseEnd_470212 : Nat := 241444765512019527087541

theorem tailTrace_470212 : CollatzResearch.WordTrace tailWord_470212 prefixEnd_470212 241444765512019527087541 := by
  unfold tailWord_470212
  simp only [CollatzResearch.WordTrace]
  refine ⟨8575020286254852330618445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11433360381673136440824593 8575020286254852330618445)
  ·
    refine ⟨3215632607345569623981917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8575020286254852330618445 3215632607345569623981917)
    ·
      refine ⟨1205862227754588608993219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3215632607345569623981917 1205862227754588608993219)
      ·
        refine ⟨1808793341631882913489829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1205862227754588608993219 1808793341631882913489829)
        ·
          refine ⟨339148751555978046279343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1808793341631882913489829 339148751555978046279343)
          ·
            refine ⟨508723127333967069419015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339148751555978046279343 508723127333967069419015)
            ·
              refine ⟨763084691000950604128523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508723127333967069419015 763084691000950604128523)
              ·
                refine ⟨1144627036501425906192785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763084691000950604128523 1144627036501425906192785)
                ·
                  refine ⟨858470277376069429644589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1144627036501425906192785 858470277376069429644589)
                  ·
                    refine ⟨321926354016026036116721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 858470277376069429644589 321926354016026036116721)
                    ·
                      refine ⟨241444765512019527087541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 321926354016026036116721 241444765512019527087541)
                      ·
                        rfl

theorem cell23_470212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_470212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470212 prefixEnd_470212 := by exact prefixLift 470212
  have htrace : WordTrace (prefixWord ++ tailWord_470212) baseStart_470212 baseEnd_470212 := by
    simpa [prefixWord, tailWord_470212, baseEnd_470212] using wordTrace_append hprefix tailTrace_470212
  have hstable : (prefixWord ++ tailWord_470212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470212).length < 2 ^ (prefixWord ++ tailWord_470212).sum := by decide
  have hdescent : baseEnd_470212 < baseStart_470212 := by decide
  rcases family_descends (prefixWord ++ tailWord_470212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470217 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 4, 2, 6]
def baseStart_470217 : Nat := 118140960795 + 470217 * 2 ^ 59
def prefixEnd_470217 : Nat := 4983230072969 + 3 ^ 40 * 470217 * 2
def baseEnd_470217 : Nat := 241447332915292007525017

theorem tailTrace_470217 : CollatzResearch.WordTrace tailWord_470217 prefixEnd_470217 241447332915292007525017 := by
  unfold tailWord_470217
  simp only [CollatzResearch.WordTrace]
  refine ⟨17150222937491590515168905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11433481958327727010112603 17150222937491590515168905)
  ·
    refine ⟨12862667203118692886376679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17150222937491590515168905 12862667203118692886376679)
    ·
      refine ⟨19294000804678039329565019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12862667203118692886376679 19294000804678039329565019)
      ·
        refine ⟨28941001207017058994347529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19294000804678039329565019 28941001207017058994347529)
        ·
          refine ⟨21705750905262794245760647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28941001207017058994347529 21705750905262794245760647)
          ·
            refine ⟨32558626357894191368640971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21705750905262794245760647 32558626357894191368640971)
            ·
              refine ⟨48837939536841287052961457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32558626357894191368640971 48837939536841287052961457)
              ·
                refine ⟨36628454652630965289721093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48837939536841287052961457 36628454652630965289721093)
                ·
                  refine ⟨6867835247368305991822705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36628454652630965289721093 6867835247368305991822705)
                  ·
                    refine ⟨5150876435526229493867029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6867835247368305991822705 5150876435526229493867029)
                    ·
                      refine ⟨241447332915292007525017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5150876435526229493867029 241447332915292007525017)
                      ·
                        rfl

theorem cell23_470217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_470217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470217 prefixEnd_470217 := by exact prefixLift 470217
  have htrace : WordTrace (prefixWord ++ tailWord_470217) baseStart_470217 baseEnd_470217 := by
    simpa [prefixWord, tailWord_470217, baseEnd_470217] using wordTrace_append hprefix tailTrace_470217
  have hstable : (prefixWord ++ tailWord_470217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470217).length < 2 ^ (prefixWord ++ tailWord_470217).sum := by decide
  have hdescent : baseEnd_470217 < baseStart_470217 := by decide
  rcases family_descends (prefixWord ++ tailWord_470217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470227 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 4, 7]
def baseStart_470227 : Nat := 118140960795 + 470227 * 2 ^ 59
def prefixEnd_470227 : Nat := 4983230072969 + 3 ^ 40 * 470227 * 2
def baseEnd_470227 : Nat := 80484155907278989466657

theorem tailTrace_470227 : CollatzResearch.WordTrace tailWord_470227 prefixEnd_470227 80484155907278989466657 := by
  unfold tailWord_470227
  simp only [CollatzResearch.WordTrace]
  refine ⟨17150587667455362223032935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11433725111636908148688623 17150587667455362223032935)
  ·
    refine ⟨25725881501183043334549403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17150587667455362223032935 25725881501183043334549403)
    ·
      refine ⟨38588822251774565001824105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25725881501183043334549403 38588822251774565001824105)
      ·
        refine ⟨28941616688830923751368079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38588822251774565001824105 28941616688830923751368079)
        ·
          refine ⟨43412425033246385627052119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28941616688830923751368079 43412425033246385627052119)
          ·
            refine ⟨65118637549869578440578179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43412425033246385627052119 65118637549869578440578179)
            ·
              refine ⟨97677956324804367660867269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65118637549869578440578179 97677956324804367660867269)
              ·
                refine ⟨18314616810900818936412613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97677956324804367660867269 18314616810900818936412613)
                ·
                  refine ⟨3433990652043903550577365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18314616810900818936412613 3433990652043903550577365)
                  ·
                    refine ⟨80484155907278989466657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3433990652043903550577365 80484155907278989466657)
                    ·
                      rfl

theorem cell23_470227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 7].length) (baseStart_470227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470227 prefixEnd_470227 := by exact prefixLift 470227
  have htrace : WordTrace (prefixWord ++ tailWord_470227) baseStart_470227 baseEnd_470227 := by
    simpa [prefixWord, tailWord_470227, baseEnd_470227] using wordTrace_append hprefix tailTrace_470227
  have hstable : (prefixWord ++ tailWord_470227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470227).length < 2 ^ (prefixWord ++ tailWord_470227).sum := by decide
  have hdescent : baseEnd_470227 < baseStart_470227 := by decide
  rcases family_descends (prefixWord ++ tailWord_470227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470281 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 3, 4, 2]
def baseStart_470281 : Nat := 118140960795 + 470281 * 2 ^ 59
def prefixEnd_470281 : Nat := 4983230072969 + 3 ^ 40 * 470281 * 2
def baseEnd_470281 : Nat := 241480195677179757124723

theorem tailTrace_470281 : CollatzResearch.WordTrace tailWord_470281 prefixEnd_470281 241480195677179757124723 := by
  unfold tailWord_470281
  simp only [CollatzResearch.WordTrace]
  refine ⟨17152557209259729445498697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11435038139506486296999131 17152557209259729445498697)
  ·
    refine ⟨12864417906944797084124023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17152557209259729445498697 12864417906944797084124023)
    ·
      refine ⟨19296626860417195626186035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12864417906944797084124023 19296626860417195626186035)
      ·
        refine ⟨28944940290625793439279053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19296626860417195626186035 28944940290625793439279053)
        ·
          refine ⟨10854352608984672539729645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28944940290625793439279053 10854352608984672539729645)
          ·
            refine ⟨4070382228369252202398617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10854352608984672539729645 4070382228369252202398617)
            ·
              refine ⟨3052786671276939151798963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4070382228369252202398617 3052786671276939151798963)
              ·
                refine ⟨4579180006915408727698445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3052786671276939151798963 4579180006915408727698445)
                ·
                  refine ⟨1717192502593278272886917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4579180006915408727698445 1717192502593278272886917)
                  ·
                    refine ⟨321973594236239676166297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1717192502593278272886917 321973594236239676166297)
                    ·
                      refine ⟨241480195677179757124723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 321973594236239676166297 241480195677179757124723)
                      ·
                        rfl

theorem cell23_470281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 4, 2].length) (baseStart_470281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470281 prefixEnd_470281 := by exact prefixLift 470281
  have htrace : WordTrace (prefixWord ++ tailWord_470281) baseStart_470281 baseEnd_470281 := by
    simpa [prefixWord, tailWord_470281, baseEnd_470281] using wordTrace_append hprefix tailTrace_470281
  have hstable : (prefixWord ++ tailWord_470281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470281).length < 2 ^ (prefixWord ++ tailWord_470281).sum := by decide
  have hdescent : baseEnd_470281 < baseStart_470281 := by decide
  rcases family_descends (prefixWord ++ tailWord_470281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470284 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 1, 3, 5]
def baseStart_470284 : Nat := 118140960795 + 470284 * 2 ^ 59
def prefixEnd_470284 : Nat := 4983230072969 + 3 ^ 40 * 470284 * 2
def baseEnd_470284 : Nat := 241481736119143245387209

theorem tailTrace_470284 : CollatzResearch.WordTrace tailWord_470284 prefixEnd_470284 241481736119143245387209 := by
  unfold tailWord_470284
  simp only [CollatzResearch.WordTrace]
  refine ⟨8576333314124430478928953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11435111085499240638571937 8576333314124430478928953)
  ·
    refine ⟨6432249985593322859196715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8576333314124430478928953 6432249985593322859196715)
    ·
      refine ⟨9648374978389984288795073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6432249985593322859196715 9648374978389984288795073)
      ·
        refine ⟨7236281233792488216596305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9648374978389984288795073 7236281233792488216596305)
        ·
          refine ⟨5427210925344366162447229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7236281233792488216596305 5427210925344366162447229)
          ·
            refine ⟨2035204097004137310917711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5427210925344366162447229 2035204097004137310917711)
            ·
              refine ⟨3052806145506205966376567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2035204097004137310917711 3052806145506205966376567)
              ·
                refine ⟨4579209218259308949564851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3052806145506205966376567 4579209218259308949564851)
                ·
                  refine ⟨6868813827388963424347277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4579209218259308949564851 6868813827388963424347277)
                  ·
                    refine ⟨2575805185270861284130229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6868813827388963424347277 2575805185270861284130229)
                    ·
                      refine ⟨241481736119143245387209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2575805185270861284130229 241481736119143245387209)
                      ·
                        rfl

theorem cell23_470284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_470284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470284 prefixEnd_470284 := by exact prefixLift 470284
  have htrace : WordTrace (prefixWord ++ tailWord_470284) baseStart_470284 baseEnd_470284 := by
    simpa [prefixWord, tailWord_470284, baseEnd_470284] using wordTrace_append hprefix tailTrace_470284
  have hstable : (prefixWord ++ tailWord_470284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470284).length < 2 ^ (prefixWord ++ tailWord_470284).sum := by decide
  have hdescent : baseEnd_470284 < baseStart_470284 := by decide
  rcases family_descends (prefixWord ++ tailWord_470284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470341 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 4, 5, 2]
def baseStart_470341 : Nat := 118140960795 + 470341 * 2 ^ 59
def prefixEnd_470341 : Nat := 4983230072969 + 3 ^ 40 * 470341 * 2
def baseEnd_470341 : Nat := 241511004516449522374447

theorem tailTrace_470341 : CollatzResearch.WordTrace tailWord_470341 prefixEnd_470341 241511004516449522374447 := by
  unfold tailWord_470341
  simp only [CollatzResearch.WordTrace]
  refine ⟨17154745589042359692682877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11436497059361573128455251 17154745589042359692682877)
  ·
    refine ⟨6433029595890884884756079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17154745589042359692682877 6433029595890884884756079)
    ·
      refine ⟨9649544393836327327134119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6433029595890884884756079 9649544393836327327134119)
      ·
        refine ⟨14474316590754490990701179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9649544393836327327134119 14474316590754490990701179)
        ·
          refine ⟨21711474886131736486051769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14474316590754490990701179 21711474886131736486051769)
          ·
            refine ⟨16283606164598802364538827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21711474886131736486051769 16283606164598802364538827)
            ·
              refine ⟨24425409246898203546808241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16283606164598802364538827 24425409246898203546808241)
              ·
                refine ⟨18319056935173652660106181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24425409246898203546808241 18319056935173652660106181)
                ·
                  refine ⟨3434823175345059873769909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18319056935173652660106181 3434823175345059873769909)
                  ·
                    refine ⟨322014672688599363165929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3434823175345059873769909 322014672688599363165929)
                    ·
                      refine ⟨241511004516449522374447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 322014672688599363165929 241511004516449522374447)
                      ·
                        rfl

theorem cell23_470341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 5, 2].length) (baseStart_470341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470341 prefixEnd_470341 := by exact prefixLift 470341
  have htrace : WordTrace (prefixWord ++ tailWord_470341) baseStart_470341 baseEnd_470341 := by
    simpa [prefixWord, tailWord_470341, baseEnd_470341] using wordTrace_append hprefix tailTrace_470341
  have hstable : (prefixWord ++ tailWord_470341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470341).length < 2 ^ (prefixWord ++ tailWord_470341).sum := by decide
  have hdescent : baseEnd_470341 < baseStart_470341 := by decide
  rcases family_descends (prefixWord ++ tailWord_470341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470391 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 3]
def baseStart_470391 : Nat := 118140960795 + 470391 * 2 ^ 59
def prefixEnd_470391 : Nat := 4983230072969 + 3 ^ 40 * 470391 * 2
def baseEnd_470391 : Nat := 241536678549174326749217

theorem tailTrace_470391 : CollatzResearch.WordTrace tailWord_470391 prefixEnd_470391 241536678549174326749217 := by
  unfold tailWord_470391
  simp only [CollatzResearch.WordTrace]
  refine ⟨17156569238861218232003027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11437712825907478821335351 17156569238861218232003027)
  ·
    refine ⟨25734853858291827348004541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17156569238861218232003027 25734853858291827348004541)
    ·
      refine ⟨9650570196859435255501703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25734853858291827348004541 9650570196859435255501703)
      ·
        refine ⟨14475855295289152883252555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9650570196859435255501703 14475855295289152883252555)
        ·
          refine ⟨21713782942933729324878833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14475855295289152883252555 21713782942933729324878833)
          ·
            refine ⟨16285337207200296993659125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21713782942933729324878833 16285337207200296993659125)
            ·
              refine ⟨1526750363175027843155543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16285337207200296993659125 1526750363175027843155543)
              ·
                refine ⟨2290125544762541764733315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526750363175027843155543 2290125544762541764733315)
                ·
                  refine ⟨3435188317143812647099973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2290125544762541764733315 3435188317143812647099973)
                  ·
                    refine ⟨644097809464464871331245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3435188317143812647099973 644097809464464871331245)
                    ·
                      refine ⟨241536678549174326749217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 644097809464464871331245 241536678549174326749217)
                      ·
                        rfl

theorem cell23_470391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_470391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470391 prefixEnd_470391 := by exact prefixLift 470391
  have htrace : WordTrace (prefixWord ++ tailWord_470391) baseStart_470391 baseEnd_470391 := by
    simpa [prefixWord, tailWord_470391, baseEnd_470391] using wordTrace_append hprefix tailTrace_470391
  have hstable : (prefixWord ++ tailWord_470391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470391).length < 2 ^ (prefixWord ++ tailWord_470391).sum := by decide
  have hdescent : baseEnd_470391 < baseStart_470391 := by decide
  rcases family_descends (prefixWord ++ tailWord_470391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470394 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 10]
def baseStart_470394 : Nat := 118140960795 + 470394 * 2 ^ 59
def prefixEnd_470394 : Nat := 4983230072969 + 3 ^ 40 * 470394 * 2
def baseEnd_470394 : Nat := 26837579887904201667967

theorem tailTrace_470394 : CollatzResearch.WordTrace tailWord_470394 prefixEnd_470394 26837579887904201667967 := by
  unfold tailWord_470394
  simp only [CollatzResearch.WordTrace]
  refine ⟨4289169664462587436090559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11437785771900233162908157 4289169664462587436090559)
  ·
    refine ⟨6433754496693881154135839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4289169664462587436090559 6433754496693881154135839)
    ·
      refine ⟨9650631745040821731203759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6433754496693881154135839 9650631745040821731203759)
      ·
        refine ⟨14475947617561232596805639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9650631745040821731203759 14475947617561232596805639)
        ·
          refine ⟨21713921426341848895208459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14475947617561232596805639 21713921426341848895208459)
          ·
            refine ⟨32570882139512773342812689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21713921426341848895208459 32570882139512773342812689)
            ·
              refine ⟨24428161604634580007109517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32570882139512773342812689 24428161604634580007109517)
              ·
                refine ⟨9160560601737967502666069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24428161604634580007109517 9160560601737967502666069)
                ·
                  refine ⟨26837579887904201667967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 9160560601737967502666069 26837579887904201667967)
                  ·
                    rfl

theorem cell23_470394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 10].length) (baseStart_470394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470394 prefixEnd_470394 := by exact prefixLift 470394
  have htrace : WordTrace (prefixWord ++ tailWord_470394) baseStart_470394 baseEnd_470394 := by
    simpa [prefixWord, tailWord_470394, baseEnd_470394] using wordTrace_append hprefix tailTrace_470394
  have hstable : (prefixWord ++ tailWord_470394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470394).length < 2 ^ (prefixWord ++ tailWord_470394).sum := by decide
  have hdescent : baseEnd_470394 < baseStart_470394 := by decide
  rcases family_descends (prefixWord ++ tailWord_470394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470481 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 1, 8, 3]
def baseStart_470481 : Nat := 118140960795 + 470481 * 2 ^ 59
def prefixEnd_470481 : Nat := 4983230072969 + 3 ^ 40 * 470481 * 2
def baseEnd_470481 : Nat := 241582891808078974623803

theorem tailTrace_470481 : CollatzResearch.WordTrace tailWord_470481 prefixEnd_470481 241582891808078974623803 := by
  unfold tailWord_470481
  simp only [CollatzResearch.WordTrace]
  refine ⟨17159851808535163602779297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11439901205690109068519531 17159851808535163602779297)
  ·
    refine ⟨12869888856401372702084473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17159851808535163602779297 12869888856401372702084473)
    ·
      refine ⟨9652416642301029526563355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12869888856401372702084473 9652416642301029526563355)
      ·
        refine ⟨14478624963451544289845033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9652416642301029526563355 14478624963451544289845033)
        ·
          refine ⟨10858968722588658217383775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14478624963451544289845033 10858968722588658217383775)
          ·
            refine ⟨16288453083882987326075663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10858968722588658217383775 16288453083882987326075663)
            ·
              refine ⟨24432679625824480989113495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16288453083882987326075663 24432679625824480989113495)
              ·
                refine ⟨36649019438736721483670243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24432679625824480989113495 36649019438736721483670243)
                ·
                  refine ⟨54973529158105082225505365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36649019438736721483670243 54973529158105082225505365)
                  ·
                    refine ⟨644221044821543932330141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54973529158105082225505365 644221044821543932330141)
                    ·
                      refine ⟨241582891808078974623803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 644221044821543932330141 241582891808078974623803)
                      ·
                        rfl

theorem cell23_470481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_470481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470481 prefixEnd_470481 := by exact prefixLift 470481
  have htrace : WordTrace (prefixWord ++ tailWord_470481) baseStart_470481 baseEnd_470481 := by
    simpa [prefixWord, tailWord_470481, baseEnd_470481] using wordTrace_append hprefix tailTrace_470481
  have hstable : (prefixWord ++ tailWord_470481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470481).length < 2 ^ (prefixWord ++ tailWord_470481).sum := by decide
  have hdescent : baseEnd_470481 < baseStart_470481 := by decide
  rcases family_descends (prefixWord ++ tailWord_470481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470495 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 5, 2, 2]
def baseStart_470495 : Nat := 118140960795 + 470495 * 2 ^ 59
def prefixEnd_470495 : Nat := 4983230072969 + 3 ^ 40 * 470495 * 2
def baseEnd_470495 : Nat := 241590080537241919848739

theorem tailTrace_470495 : CollatzResearch.WordTrace tailWord_470495 prefixEnd_470495 241590080537241919848739 := by
  unfold tailWord_470495
  simp only [CollatzResearch.WordTrace]
  refine ⟨17160362430484443993788939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11440241620322962662525959 17160362430484443993788939)
  ·
    refine ⟨25740543645726665990683409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17160362430484443993788939 25740543645726665990683409)
    ·
      refine ⟨19305407734294999493012557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25740543645726665990683409 19305407734294999493012557)
      ·
        refine ⟨7239527900360624809879709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19305407734294999493012557 7239527900360624809879709)
        ·
          refine ⟨2714822962635234303704891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7239527900360624809879709 2714822962635234303704891)
          ·
            refine ⟨4072234443952851455557337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2714822962635234303704891 4072234443952851455557337)
            ·
              refine ⟨3054175832964638591668003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4072234443952851455557337 3054175832964638591668003)
              ·
                refine ⟨4581263749446957887502005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3054175832964638591668003 4581263749446957887502005)
                ·
                  refine ⟨429493476510652301953313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4581263749446957887502005 429493476510652301953313)
                  ·
                    refine ⟨322120107382989226464985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 429493476510652301953313 322120107382989226464985)
                    ·
                      refine ⟨241590080537241919848739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 322120107382989226464985 241590080537241919848739)
                      ·
                        rfl

theorem cell23_470495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_470495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470495 prefixEnd_470495 := by exact prefixLift 470495
  have htrace : WordTrace (prefixWord ++ tailWord_470495) baseStart_470495 baseEnd_470495 := by
    simpa [prefixWord, tailWord_470495, baseEnd_470495] using wordTrace_append hprefix tailTrace_470495
  have hstable : (prefixWord ++ tailWord_470495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470495).length < 2 ^ (prefixWord ++ tailWord_470495).sum := by decide
  have hdescent : baseEnd_470495 < baseStart_470495 := by decide
  rcases family_descends (prefixWord ++ tailWord_470495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470545 : List Nat := [1, 2, 2, 1, 1, 2, 3, 5, 2, 1, 3]
def baseStart_470545 : Nat := 118140960795 + 470545 * 2 ^ 59
def prefixEnd_470545 : Nat := 4983230072969 + 3 ^ 40 * 470545 * 2
def baseEnd_470545 : Nat := 241615754569966724223509

theorem tailTrace_470545 : CollatzResearch.WordTrace tailWord_470545 prefixEnd_470545 241615754569966724223509 := by
  unfold tailWord_470545
  simp only [CollatzResearch.WordTrace]
  refine ⟨17162186080303302533109089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11441457386868868355406059 17162186080303302533109089)
  ·
    refine ⟨12871639560227476899831817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17162186080303302533109089 12871639560227476899831817)
    ·
      refine ⟨9653729670170607674873863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12871639560227476899831817 9653729670170607674873863)
      ·
        refine ⟨14480594505255911512310795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9653729670170607674873863 14480594505255911512310795)
        ·
          refine ⟨21720891757883867268466193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14480594505255911512310795 21720891757883867268466193)
          ·
            refine ⟨16290668818412900451349645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21720891757883867268466193 16290668818412900451349645)
            ·
              refine ⟨6109000806904837669256117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16290668818412900451349645 6109000806904837669256117)
              ·
                refine ⟨572718825647328531492761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6109000806904837669256117 572718825647328531492761)
                ·
                  refine ⟨429539119235496398619571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572718825647328531492761 429539119235496398619571)
                  ·
                    refine ⟨644308678853244597929357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 429539119235496398619571 644308678853244597929357)
                    ·
                      refine ⟨241615754569966724223509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 644308678853244597929357 241615754569966724223509)
                      ·
                        rfl

theorem cell23_470545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 1, 3].length) (baseStart_470545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470545 prefixEnd_470545 := by exact prefixLift 470545
  have htrace : WordTrace (prefixWord ++ tailWord_470545) baseStart_470545 baseEnd_470545 := by
    simpa [prefixWord, tailWord_470545, baseEnd_470545] using wordTrace_append hprefix tailTrace_470545
  have hstable : (prefixWord ++ tailWord_470545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470545).length < 2 ^ (prefixWord ++ tailWord_470545).sum := by decide
  have hdescent : baseEnd_470545 < baseStart_470545 := by decide
  rcases family_descends (prefixWord ++ tailWord_470545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470601 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 9]
def baseStart_470601 : Nat := 118140960795 + 470601 * 2 ^ 59
def prefixEnd_470601 : Nat := 4983230072969 + 3 ^ 40 * 470601 * 2
def baseEnd_470601 : Nat := 241644509486618505123251

theorem tailTrace_470601 : CollatzResearch.WordTrace tailWord_470601 prefixEnd_470601 241644509486618505123251 := by
  unfold tailWord_470601
  simp only [CollatzResearch.WordTrace]
  refine ⟨17164228568100424097147657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11442819045400282731431771 17164228568100424097147657)
  ·
    refine ⟨12873171426075318072860743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17164228568100424097147657 12873171426075318072860743)
    ·
      refine ⟨19309757139112977109291115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12873171426075318072860743 19309757139112977109291115)
      ·
        refine ⟨28964635708669465663936673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19309757139112977109291115 28964635708669465663936673)
        ·
          refine ⟨21723476781502099247952505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28964635708669465663936673 21723476781502099247952505)
          ·
            refine ⟨16292607586126574435964379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21723476781502099247952505 16292607586126574435964379)
            ·
              refine ⟨24438911379189861653946569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16292607586126574435964379 24438911379189861653946569)
              ·
                refine ⟨18329183534392396240459927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24438911379189861653946569 18329183534392396240459927)
                ·
                  refine ⟨27493775301588594360689891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18329183534392396240459927 27493775301588594360689891)
                  ·
                    refine ⟨41240662952382891541034837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27493775301588594360689891 41240662952382891541034837)
                    ·
                      refine ⟨241644509486618505123251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 41240662952382891541034837 241644509486618505123251)
                      ·
                        rfl

theorem cell23_470601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_470601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470601 prefixEnd_470601 := by exact prefixLift 470601
  have htrace : WordTrace (prefixWord ++ tailWord_470601) baseStart_470601 baseEnd_470601 := by
    simpa [prefixWord, tailWord_470601, baseEnd_470601] using wordTrace_append hprefix tailTrace_470601
  have hstable : (prefixWord ++ tailWord_470601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470601).length < 2 ^ (prefixWord ++ tailWord_470601).sum := by decide
  have hdescent : baseEnd_470601 < baseStart_470601 := by decide
  rcases family_descends (prefixWord ++ tailWord_470601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470611 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 8]
def baseStart_470611 : Nat := 118140960795 + 470611 * 2 ^ 59
def prefixEnd_470611 : Nat := 4983230072969 + 3 ^ 40 * 470611 * 2
def baseEnd_470611 : Nat := 241649644293163465998205

theorem tailTrace_470611 : CollatzResearch.WordTrace tailWord_470611 prefixEnd_470611 241649644293163465998205 := by
  unfold tailWord_470611
  simp only [CollatzResearch.WordTrace]
  refine ⟨17164593298064195805011687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11443062198709463870007791 17164593298064195805011687)
  ·
    refine ⟨25746889947096293707517531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17164593298064195805011687 25746889947096293707517531)
    ·
      refine ⟨38620334920644440561276297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25746889947096293707517531 38620334920644440561276297)
      ·
        refine ⟨28965251190483330420957223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38620334920644440561276297 28965251190483330420957223)
        ·
          refine ⟨43447876785724995631435835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28965251190483330420957223 43447876785724995631435835)
          ·
            refine ⟨65171815178587493447153753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43447876785724995631435835 65171815178587493447153753)
            ·
              refine ⟨48878861383940620085365315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65171815178587493447153753 48878861383940620085365315)
              ·
                refine ⟨73318292075910930128047973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48878861383940620085365315 73318292075910930128047973)
                ·
                  refine ⟨13747179764233299399008995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73318292075910930128047973 13747179764233299399008995)
                  ·
                    refine ⟨20620769646349949098513493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13747179764233299399008995 20620769646349949098513493)
                    ·
                      refine ⟨241649644293163465998205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 20620769646349949098513493 241649644293163465998205)
                      ·
                        rfl

theorem cell23_470611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_470611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470611 prefixEnd_470611 := by exact prefixLift 470611
  have htrace : WordTrace (prefixWord ++ tailWord_470611) baseStart_470611 baseEnd_470611 := by
    simpa [prefixWord, tailWord_470611, baseEnd_470611] using wordTrace_append hprefix tailTrace_470611
  have hstable : (prefixWord ++ tailWord_470611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470611).length < 2 ^ (prefixWord ++ tailWord_470611).sum := by decide
  have hdescent : baseEnd_470611 < baseStart_470611 := by decide
  rcases family_descends (prefixWord ++ tailWord_470611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470618 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3]
def baseStart_470618 : Nat := 118140960795 + 470618 * 2 ^ 59
def prefixEnd_470618 : Nat := 4983230072969 + 3 ^ 40 * 470618 * 2
def baseEnd_470618 : Nat := 241653238657744938610673

theorem tailTrace_470618 : CollatzResearch.WordTrace tailWord_470618 prefixEnd_470618 241653238657744938610673 := by
  unfold tailWord_470618
  simp only [CollatzResearch.WordTrace]
  refine ⟨4291212152259709000129127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11443232406025890667011005 4291212152259709000129127)
  ·
    refine ⟨6436818228389563500193691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4291212152259709000129127 6436818228389563500193691)
    ·
      refine ⟨9655227342584345250290537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6436818228389563500193691 9655227342584345250290537)
      ·
        refine ⟨7241420506938258937717903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9655227342584345250290537 7241420506938258937717903)
        ·
          refine ⟨10862130760407388406576855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7241420506938258937717903 10862130760407388406576855)
          ·
            refine ⟨16293196140611082609865283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10862130760407388406576855 16293196140611082609865283)
            ·
              refine ⟨24439794210916623914797925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16293196140611082609865283 24439794210916623914797925)
              ·
                refine ⟨4582461414546866984024611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24439794210916623914797925 4582461414546866984024611)
                ·
                  refine ⟨6873692121820300476036917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4582461414546866984024611 6873692121820300476036917)
                  ·
                    refine ⟨644408636420653169628461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6873692121820300476036917 644408636420653169628461)
                    ·
                      refine ⟨241653238657744938610673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 644408636420653169628461 241653238657744938610673)
                      ·
                        rfl

theorem cell23_470618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_470618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470618 prefixEnd_470618 := by exact prefixLift 470618
  have htrace : WordTrace (prefixWord ++ tailWord_470618) baseStart_470618 baseEnd_470618 := by
    simpa [prefixWord, tailWord_470618, baseEnd_470618] using wordTrace_append hprefix tailTrace_470618
  have hstable : (prefixWord ++ tailWord_470618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470618).length < 2 ^ (prefixWord ++ tailWord_470618).sum := by decide
  have hdescent : baseEnd_470618 < baseStart_470618 := by decide
  rcases family_descends (prefixWord ++ tailWord_470618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470709 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 2, 4, 2]
def baseStart_470709 : Nat := 118140960795 + 470709 * 2 ^ 59
def prefixEnd_470709 : Nat := 4983230072969 + 3 ^ 40 * 470709 * 2
def baseEnd_470709 : Nat := 241699965397304082572755

theorem tailTrace_470709 : CollatzResearch.WordTrace tailWord_470709 prefixEnd_470709 241699965397304082572755 := by
  unfold tailWord_470709
  simp only [CollatzResearch.WordTrace]
  refine ⟨17168167651709158542079181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11445445101139439028052787 17168167651709158542079181)
  ·
    refine ⟨6438062869390934453279693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17168167651709158542079181 6438062869390934453279693)
    ·
      refine ⟨2414273576021600419979885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6438062869390934453279693 2414273576021600419979885)
      ·
        refine ⟨905352591008100157492457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2414273576021600419979885 905352591008100157492457)
        ·
          refine ⟨679014443256075118119343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 905352591008100157492457 679014443256075118119343)
          ·
            refine ⟨1018521664884112677179015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679014443256075118119343 1018521664884112677179015)
            ·
              refine ⟨1527782497326169015768523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1018521664884112677179015 1527782497326169015768523)
              ·
                refine ⟨2291673745989253523652785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1527782497326169015768523 2291673745989253523652785)
                ·
                  refine ⟨1718755309491940142739589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2291673745989253523652785 1718755309491940142739589)
                  ·
                    refine ⟨322266620529738776763673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1718755309491940142739589 322266620529738776763673)
                    ·
                      refine ⟨241699965397304082572755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 322266620529738776763673 241699965397304082572755)
                      ·
                        rfl

theorem cell23_470709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_470709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470709 prefixEnd_470709 := by exact prefixLift 470709
  have htrace : WordTrace (prefixWord ++ tailWord_470709) baseStart_470709 baseEnd_470709 := by
    simpa [prefixWord, tailWord_470709, baseEnd_470709] using wordTrace_append hprefix tailTrace_470709
  have hstable : (prefixWord ++ tailWord_470709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470709).length < 2 ^ (prefixWord ++ tailWord_470709).sum := by decide
  have hdescent : baseEnd_470709 < baseStart_470709 := by decide
  rcases family_descends (prefixWord ++ tailWord_470709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470726 : List Nat := [6, 1, 2, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_470726 : Nat := 118140960795 + 470726 * 2 ^ 59
def prefixEnd_470726 : Nat := 4983230072969 + 3 ^ 40 * 470726 * 2
def baseEnd_470726 : Nat := 241708694568430516060177

theorem tailTrace_470726 : CollatzResearch.WordTrace tailWord_470726 prefixEnd_470726 241708694568430516060177 := by
  unfold tailWord_470726
  simp only [CollatzResearch.WordTrace]
  refine ⟨536524615395236576420251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11445858461765046963632021 536524615395236576420251)
  ·
    refine ⟨804786923092854864630377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 536524615395236576420251 804786923092854864630377)
    ·
      refine ⟨603590192319641148472783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 804786923092854864630377 603590192319641148472783)
      ·
        refine ⟨905385288479461722709175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603590192319641148472783 905385288479461722709175)
        ·
          refine ⟨1358077932719192584063763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905385288479461722709175 1358077932719192584063763)
          ·
            refine ⟨2037116899078788876095645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1358077932719192584063763 2037116899078788876095645)
            ·
              refine ⟨763918837154545828535867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2037116899078788876095645 763918837154545828535867)
              ·
                refine ⟨1145878255731818742803801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763918837154545828535867 1145878255731818742803801)
                ·
                  refine ⟨859408691798864057102851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1145878255731818742803801 859408691798864057102851)
                  ·
                    refine ⟨1289113037698296085654277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 859408691798864057102851 1289113037698296085654277)
                    ·
                      refine ⟨241708694568430516060177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1289113037698296085654277 241708694568430516060177)
                      ·
                        rfl

theorem cell23_470726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_470726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470726 prefixEnd_470726 := by exact prefixLift 470726
  have htrace : WordTrace (prefixWord ++ tailWord_470726) baseStart_470726 baseEnd_470726 := by
    simpa [prefixWord, tailWord_470726, baseEnd_470726] using wordTrace_append hprefix tailTrace_470726
  have hstable : (prefixWord ++ tailWord_470726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470726).length < 2 ^ (prefixWord ++ tailWord_470726).sum := by decide
  have hdescent : baseEnd_470726 < baseStart_470726 := by decide
  rcases family_descends (prefixWord ++ tailWord_470726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470752 : List Nat := [2, 1, 1, 3, 1, 2, 2, 4, 2, 3, 2]
def baseStart_470752 : Nat := 118140960795 + 470752 * 2 ^ 59
def prefixEnd_470752 : Nat := 4983230072969 + 3 ^ 40 * 470752 * 2
def baseEnd_470752 : Nat := 241722045065447414335057

theorem tailTrace_470752 : CollatzResearch.WordTrace tailWord_470752 prefixEnd_470752 241722045065447414335057 := by
  unfold tailWord_470752
  simp only [CollatzResearch.WordTrace]
  refine ⟨8584867995276688442947255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11446490660368917923929673 8584867995276688442947255)
  ·
    refine ⟨12877301992915032664420883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8584867995276688442947255 12877301992915032664420883)
    ·
      refine ⟨19315952989372548996631325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12877301992915032664420883 19315952989372548996631325)
      ·
        refine ⟨7243482371014705873736747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19315952989372548996631325 7243482371014705873736747)
        ·
          refine ⟨10865223556522058810605121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7243482371014705873736747 10865223556522058810605121)
          ·
            refine ⟨8148917667391544107953841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10865223556522058810605121 8148917667391544107953841)
            ·
              refine ⟨6111688250543658080965381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8148917667391544107953841 6111688250543658080965381)
              ·
                refine ⟨1145941546976935890181009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6111688250543658080965381 1145941546976935890181009)
                ·
                  refine ⟨859456160232701917635757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1145941546976935890181009 859456160232701917635757)
                  ·
                    refine ⟨322296060087263219113409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 859456160232701917635757 322296060087263219113409)
                    ·
                      refine ⟨241722045065447414335057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 322296060087263219113409 241722045065447414335057)
                      ·
                        rfl

theorem cell23_470752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_470752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470752 prefixEnd_470752 := by exact prefixLift 470752
  have htrace : WordTrace (prefixWord ++ tailWord_470752) baseStart_470752 baseEnd_470752 := by
    simpa [prefixWord, tailWord_470752, baseEnd_470752] using wordTrace_append hprefix tailTrace_470752
  have hstable : (prefixWord ++ tailWord_470752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470752).length < 2 ^ (prefixWord ++ tailWord_470752).sum := by decide
  have hdescent : baseEnd_470752 < baseStart_470752 := by decide
  rcases family_descends (prefixWord ++ tailWord_470752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470775 : List Nat := [1, 1, 3, 1, 1, 1, 7, 1, 1, 6]
def baseStart_470775 : Nat := 118140960795 + 470775 * 2 ^ 59
def prefixEnd_470775 : Nat := 4983230072969 + 3 ^ 40 * 470775 * 2
def baseEnd_470775 : Nat := 80577951706833608115817

theorem tailTrace_470775 : CollatzResearch.WordTrace tailWord_470775 prefixEnd_470775 80577951706833608115817 := by
  unfold tailWord_470775
  simp only [CollatzResearch.WordTrace]
  refine ⟨17170574869470051813981779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11447049912980034542654519 17170574869470051813981779)
  ·
    refine ⟨25755862304205077720972669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17170574869470051813981779 25755862304205077720972669)
    ·
      refine ⟨9658448364076904145364751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25755862304205077720972669 9658448364076904145364751)
      ·
        refine ⟨14487672546115356218047127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9658448364076904145364751 14487672546115356218047127)
        ·
          refine ⟨21731508819173034327070691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14487672546115356218047127 21731508819173034327070691)
          ·
            refine ⟨32597263228759551490606037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21731508819173034327070691 32597263228759551490606037)
            ·
              refine ⟨763998356924051988061079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 32597263228759551490606037 763998356924051988061079)
              ·
                refine ⟨1145997535386077982091619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763998356924051988061079 1145997535386077982091619)
                ·
                  refine ⟨1718996303079116973137429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1145997535386077982091619 1718996303079116973137429)
                  ·
                    refine ⟨80577951706833608115817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1718996303079116973137429 80577951706833608115817)
                    ·
                      rfl

theorem cell23_470775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_470775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470775 prefixEnd_470775 := by exact prefixLift 470775
  have htrace : WordTrace (prefixWord ++ tailWord_470775) baseStart_470775 baseEnd_470775 := by
    simpa [prefixWord, tailWord_470775, baseEnd_470775] using wordTrace_append hprefix tailTrace_470775
  have hstable : (prefixWord ++ tailWord_470775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470775).length < 2 ^ (prefixWord ++ tailWord_470775).sum := by decide
  have hdescent : baseEnd_470775 < baseStart_470775 := by decide
  rcases family_descends (prefixWord ++ tailWord_470775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470795 : List Nat := [1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 4]
def baseStart_470795 : Nat := 118140960795 + 470795 * 2 ^ 59
def prefixEnd_470795 : Nat := 4983230072969 + 3 ^ 40 * 470795 * 2
def baseEnd_470795 : Nat := 241744124733590746097359

theorem tailTrace_470795 : CollatzResearch.WordTrace tailWord_470795 prefixEnd_470795 241744124733590746097359 := by
  unfold tailWord_470795
  simp only [CollatzResearch.WordTrace]
  refine ⟨17171304329397595229709839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11447536219598396819806559 17171304329397595229709839)
  ·
    refine ⟨25756956494096392844564759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17171304329397595229709839 25756956494096392844564759)
    ·
      refine ⟨38635434741144589266847139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25756956494096392844564759 38635434741144589266847139)
      ·
        refine ⟨57953152111716883900270709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38635434741144589266847139 57953152111716883900270709)
        ·
          refine ⟨5433108010473457865650379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57953152111716883900270709 5433108010473457865650379)
          ·
            refine ⟨8149662015710186798475569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5433108010473457865650379 8149662015710186798475569)
            ·
              refine ⟨6112246511782640098856677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8149662015710186798475569 6112246511782640098856677)
              ·
                refine ⟨1146046220959245018535627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6112246511782640098856677 1146046220959245018535627)
                ·
                  refine ⟨1719069331438867527803441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1146046220959245018535627 1719069331438867527803441)
                  ·
                    refine ⟨1289301998579150645852581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1719069331438867527803441 1289301998579150645852581)
                    ·
                      refine ⟨241744124733590746097359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1289301998579150645852581 241744124733590746097359)
                      ·
                        rfl

theorem cell23_470795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 4].length) (baseStart_470795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470795 prefixEnd_470795 := by exact prefixLift 470795
  have htrace : WordTrace (prefixWord ++ tailWord_470795) baseStart_470795 baseEnd_470795 := by
    simpa [prefixWord, tailWord_470795, baseEnd_470795] using wordTrace_append hprefix tailTrace_470795
  have hstable : (prefixWord ++ tailWord_470795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470795).length < 2 ^ (prefixWord ++ tailWord_470795).sum := by decide
  have hdescent : baseEnd_470795 < baseStart_470795 := by decide
  rcases family_descends (prefixWord ++ tailWord_470795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470805 : List Nat := [1, 3, 2, 1, 2, 5, 9]
def baseStart_470805 : Nat := 118140960795 + 470805 * 2 ^ 59
def prefixEnd_470805 : Nat := 4983230072969 + 3 ^ 40 * 470805 * 2
def baseEnd_470805 : Nat := 2984558759754761814473

theorem tailTrace_470805 : CollatzResearch.WordTrace tailWord_470805 prefixEnd_470805 2984558759754761814473 := by
  unfold tailWord_470805
  simp only [CollatzResearch.WordTrace]
  refine ⟨17171669059361366937573869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11447779372907577958382579 17171669059361366937573869)
  ·
    refine ⟨6439375897260512601590201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17171669059361366937573869 6439375897260512601590201)
    ·
      refine ⟨4829531922945384451192651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6439375897260512601590201 4829531922945384451192651)
      ·
        refine ⟨7244297884418076676788977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4829531922945384451192651 7244297884418076676788977)
        ·
          refine ⟨5433223413313557507591733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7244297884418076676788977 5433223413313557507591733)
          ·
            refine ⟨509364694998146016336725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5433223413313557507591733 509364694998146016336725)
            ·
              refine ⟨2984558759754761814473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 509364694998146016336725 2984558759754761814473)
              ·
                rfl

theorem cell23_470805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 9].length) (baseStart_470805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470805 prefixEnd_470805 := by exact prefixLift 470805
  have htrace : WordTrace (prefixWord ++ tailWord_470805) baseStart_470805 baseEnd_470805 := by
    simpa [prefixWord, tailWord_470805, baseEnd_470805] using wordTrace_append hprefix tailTrace_470805
  have hstable : (prefixWord ++ tailWord_470805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470805).length < 2 ^ (prefixWord ++ tailWord_470805).sum := by decide
  have hdescent : baseEnd_470805 < baseStart_470805 := by decide
  rcases family_descends (prefixWord ++ tailWord_470805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470836 : List Nat := [2, 5, 1, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_470836 : Nat := 118140960795 + 470836 * 2 ^ 59
def prefixEnd_470836 : Nat := 4983230072969 + 3 ^ 40 * 470836 * 2
def baseEnd_470836 : Nat := 241765177440425085684671

theorem tailTrace_470836 : CollatzResearch.WordTrace tailWord_470836 prefixEnd_470836 241765177440425085684671 := by
  unfold tailWord_470836
  simp only [CollatzResearch.WordTrace]
  refine ⟨8586399861124529615976181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11448533148166039487968241 8586399861124529615976181)
  ·
    refine ⟨804974986980424651497767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8586399861124529615976181 804974986980424651497767)
    ·
      refine ⟨1207462480470636977246651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 804974986980424651497767 1207462480470636977246651)
      ·
        refine ⟨1811193720705955465869977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1207462480470636977246651 1811193720705955465869977)
        ·
          refine ⟨1358395290529466599402483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1811193720705955465869977 1358395290529466599402483)
          ·
            refine ⟨2037592935794199899103725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1358395290529466599402483 2037592935794199899103725)
            ·
              refine ⟨764097350922824962163897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2037592935794199899103725 764097350922824962163897)
              ·
                refine ⟨573073013192118721622923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 764097350922824962163897 573073013192118721622923)
                ·
                  refine ⟨859609519788178082434385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 573073013192118721622923 859609519788178082434385)
                  ·
                    refine ⟨644707139841133561825789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 859609519788178082434385 644707139841133561825789)
                    ·
                      refine ⟨241765177440425085684671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 644707139841133561825789 241765177440425085684671)
                      ·
                        rfl

theorem cell23_470836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_470836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470836 prefixEnd_470836 := by exact prefixLift 470836
  have htrace : WordTrace (prefixWord ++ tailWord_470836) baseStart_470836 baseEnd_470836 := by
    simpa [prefixWord, tailWord_470836, baseEnd_470836] using wordTrace_append hprefix tailTrace_470836
  have hstable : (prefixWord ++ tailWord_470836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470836).length < 2 ^ (prefixWord ++ tailWord_470836).sum := by decide
  have hdescent : baseEnd_470836 < baseStart_470836 := by decide
  rcases family_descends (prefixWord ++ tailWord_470836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470866 : List Nat := [3, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_470866 : Nat := 118140960795 + 470866 * 2 ^ 59
def prefixEnd_470866 : Nat := 4983230072969 + 3 ^ 40 * 470866 * 2
def baseEnd_470866 : Nat := 241780581860059968309533

theorem tailTrace_470866 : CollatzResearch.WordTrace tailWord_470866 prefixEnd_470866 241780581860059968309533 := by
  unfold tailWord_470866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4293473478035093588886113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11449262608093582903696301 4293473478035093588886113)
  ·
    refine ⟨3220105108526320191664585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4293473478035093588886113 3220105108526320191664585)
    ·
      refine ⟨2415078831394740143748439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3220105108526320191664585 2415078831394740143748439)
      ·
        refine ⟨3622618247092110215622659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2415078831394740143748439 3622618247092110215622659)
        ·
          refine ⟨5433927370638165323433989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3622618247092110215622659 5433927370638165323433989)
          ·
            refine ⟨1018861381994655998143873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5433927370638165323433989 1018861381994655998143873)
            ·
              refine ⟨764146036495991998607905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1018861381994655998143873 764146036495991998607905)
              ·
                refine ⟨573109527371993998955929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 764146036495991998607905 573109527371993998955929)
                ·
                  refine ⟨429832145528995499216947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573109527371993998955929 429832145528995499216947)
                  ·
                    refine ⟨644748218293493248825421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 429832145528995499216947 644748218293493248825421)
                    ·
                      refine ⟨241780581860059968309533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 644748218293493248825421 241780581860059968309533)
                      ·
                        rfl

theorem cell23_470866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_470866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470866 prefixEnd_470866 := by exact prefixLift 470866
  have htrace : WordTrace (prefixWord ++ tailWord_470866) baseStart_470866 baseEnd_470866 := by
    simpa [prefixWord, tailWord_470866, baseEnd_470866] using wordTrace_append hprefix tailTrace_470866
  have hstable : (prefixWord ++ tailWord_470866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470866).length < 2 ^ (prefixWord ++ tailWord_470866).sum := by decide
  have hdescent : baseEnd_470866 < baseStart_470866 := by decide
  rcases family_descends (prefixWord ++ tailWord_470866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470882 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_470882 : Nat := 118140960795 + 470882 * 2 ^ 59
def prefixEnd_470882 : Nat := 4983230072969 + 3 ^ 40 * 470882 * 2
def baseEnd_470882 : Nat := 80596265850177301903153

theorem tailTrace_470882 : CollatzResearch.WordTrace tailWord_470882 prefixEnd_470882 80596265850177301903153 := by
  unfold tailWord_470882
  simp only [CollatzResearch.WordTrace]
  refine ⟨4293619370020602272031725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11449651653388272725417933 4293619370020602272031725)
  ·
    refine ⟨1610107263757725852011897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4293619370020602272031725 1610107263757725852011897)
    ·
      refine ⟨1207580447818294389008923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1610107263757725852011897 1207580447818294389008923)
      ·
        refine ⟨1811370671727441583513385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1207580447818294389008923 1811370671727441583513385)
        ·
          refine ⟨1358528003795581187635039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1811370671727441583513385 1358528003795581187635039)
          ·
            refine ⟨2037792005693371781452559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1358528003795581187635039 2037792005693371781452559)
            ·
              refine ⟨3056688008540057672178839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2037792005693371781452559 3056688008540057672178839)
              ·
                refine ⟨4585032012810086508268259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3056688008540057672178839 4585032012810086508268259)
                ·
                  refine ⟨6877548019215129762402389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4585032012810086508268259 6877548019215129762402389)
                  ·
                    refine ⟨80596265850177301903153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6877548019215129762402389 80596265850177301903153)
                    ·
                      rfl

theorem cell23_470882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_470882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470882 prefixEnd_470882 := by exact prefixLift 470882
  have htrace : WordTrace (prefixWord ++ tailWord_470882) baseStart_470882 baseEnd_470882 := by
    simpa [prefixWord, tailWord_470882, baseEnd_470882] using wordTrace_append hprefix tailTrace_470882
  have hstable : (prefixWord ++ tailWord_470882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470882).length < 2 ^ (prefixWord ++ tailWord_470882).sum := by decide
  have hdescent : baseEnd_470882 < baseStart_470882 := by decide
  rcases family_descends (prefixWord ++ tailWord_470882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470910 : List Nat := [4, 2, 3, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_470910 : Nat := 118140960795 + 470910 * 2 ^ 59
def prefixEnd_470910 : Nat := 4983230072969 + 3 ^ 40 * 470910 * 2
def baseEnd_470910 : Nat := 241803175008857796159331

theorem tailTrace_470910 : CollatzResearch.WordTrace tailWord_470910 prefixEnd_470910 241803175008857796159331 := by
  unfold tailWord_470910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2146937340497621233768273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11450332482653979913430789 2146937340497621233768273)
  ·
    refine ⟨1610203005373215925326205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2146937340497621233768273 1610203005373215925326205)
    ·
      refine ⟨603826127014955971997327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1610203005373215925326205 603826127014955971997327)
      ·
        refine ⟨905739190522433957995991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603826127014955971997327 905739190522433957995991)
        ·
          refine ⟨1358608785783650936993987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905739190522433957995991 1358608785783650936993987)
          ·
            refine ⟨2037913178675476405490981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1358608785783650936993987 2037913178675476405490981)
            ·
              refine ⟨382108721001651826029559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2037913178675476405490981 382108721001651826029559)
              ·
                refine ⟨573163081502477739044339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382108721001651826029559 573163081502477739044339)
                ·
                  refine ⟨859744622253716608566509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 573163081502477739044339 859744622253716608566509)
                  ·
                    refine ⟨322404233345143728212441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 859744622253716608566509 322404233345143728212441)
                    ·
                      refine ⟨241803175008857796159331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 322404233345143728212441 241803175008857796159331)
                      ·
                        rfl

theorem cell23_470910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_470910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470910 prefixEnd_470910 := by exact prefixLift 470910
  have htrace : WordTrace (prefixWord ++ tailWord_470910) baseStart_470910 baseEnd_470910 := by
    simpa [prefixWord, tailWord_470910, baseEnd_470910] using wordTrace_append hprefix tailTrace_470910
  have hstable : (prefixWord ++ tailWord_470910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470910).length < 2 ^ (prefixWord ++ tailWord_470910).sum := by decide
  have hdescent : baseEnd_470910 < baseStart_470910 := by decide
  rcases family_descends (prefixWord ++ tailWord_470910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470940 : List Nat := [2, 2, 3, 3, 1, 2, 3, 1, 2, 2, 2]
def baseStart_470940 : Nat := 118140960795 + 470940 * 2 ^ 59
def prefixEnd_470940 : Nat := 4983230072969 + 3 ^ 40 * 470940 * 2
def baseEnd_470940 : Nat := 241818579428492678784193

theorem tailTrace_470940 : CollatzResearch.WordTrace tailWord_470940 prefixEnd_470940 241818579428492678784193 := by
  unfold tailWord_470940
  simp only [CollatzResearch.WordTrace]
  refine ⟨8588296456936142496869137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11451061942581523329158849 8588296456936142496869137)
  ·
    refine ⟨6441222342702106872651853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8588296456936142496869137 6441222342702106872651853)
    ·
      refine ⟨2415458378513290077244445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6441222342702106872651853 2415458378513290077244445)
      ·
        refine ⟨905796891942483778966667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2415458378513290077244445 905796891942483778966667)
        ·
          refine ⟨1358695337913725668450001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905796891942483778966667 1358695337913725668450001)
          ·
            refine ⟨1019021503435294251337501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1358695337913725668450001 1019021503435294251337501)
            ·
              refine ⟨382133063788235344251563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1019021503435294251337501 382133063788235344251563)
              ·
                refine ⟨573199595682353016377345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382133063788235344251563 573199595682353016377345)
                ·
                  refine ⟨429899696761764762283009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573199595682353016377345 429899696761764762283009)
                  ·
                    refine ⟨322424772571323571712257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 429899696761764762283009 322424772571323571712257)
                    ·
                      refine ⟨241818579428492678784193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 322424772571323571712257 241818579428492678784193)
                      ·
                        rfl

theorem cell23_470940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_470940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470940 prefixEnd_470940 := by exact prefixLift 470940
  have htrace : WordTrace (prefixWord ++ tailWord_470940) baseStart_470940 baseEnd_470940 := by
    simpa [prefixWord, tailWord_470940, baseEnd_470940] using wordTrace_append hprefix tailTrace_470940
  have hstable : (prefixWord ++ tailWord_470940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470940).length < 2 ^ (prefixWord ++ tailWord_470940).sum := by decide
  have hdescent : baseEnd_470940 < baseStart_470940 := by decide
  rcases family_descends (prefixWord ++ tailWord_470940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470962 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_470962 : Nat := 118140960795 + 470962 * 2 ^ 59
def prefixEnd_470962 : Nat := 4983230072969 + 3 ^ 40 * 470962 * 2
def baseEnd_470962 : Nat := 241829876002891592709091

theorem tailTrace_470962 : CollatzResearch.WordTrace tailWord_470962 prefixEnd_470962 241829876002891592709091 := by
  unfold tailWord_470962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4294348829948145687759785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11451596879861721834026093 4294348829948145687759785)
  ·
    refine ⟨3220761622461109265819839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4294348829948145687759785 3220761622461109265819839)
    ·
      refine ⟨4831142433691663898729759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3220761622461109265819839 4831142433691663898729759)
      ·
        refine ⟨7246713650537495848094639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4831142433691663898729759 7246713650537495848094639)
        ·
          refine ⟨10870070475806243772141959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7246713650537495848094639 10870070475806243772141959)
          ·
            refine ⟨16305105713709365658212939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10870070475806243772141959 16305105713709365658212939)
            ·
              refine ⟨24457658570564048487319409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16305105713709365658212939 24457658570564048487319409)
              ·
                refine ⟨18343243927923036365489557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24457658570564048487319409 18343243927923036365489557)
                ·
                  refine ⟨859839559121392329632323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18343243927923036365489557 859839559121392329632323)
                  ·
                    refine ⟨1289759338682088494448485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 859839559121392329632323 1289759338682088494448485)
                    ·
                      refine ⟨241829876002891592709091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1289759338682088494448485 241829876002891592709091)
                      ·
                        rfl

theorem cell23_470962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_470962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_470962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_470962 prefixEnd_470962 := by exact prefixLift 470962
  have htrace : WordTrace (prefixWord ++ tailWord_470962) baseStart_470962 baseEnd_470962 := by
    simpa [prefixWord, tailWord_470962, baseEnd_470962] using wordTrace_append hprefix tailTrace_470962
  have hstable : (prefixWord ++ tailWord_470962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470962).length < 2 ^ (prefixWord ++ tailWord_470962).sum := by decide
  have hdescent : baseEnd_470962 < baseStart_470962 := by decide
  rcases family_descends (prefixWord ++ tailWord_470962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471063 : List Nat := [1, 1, 3, 5, 2, 1, 1, 2, 3, 1, 3]
def baseStart_471063 : Nat := 118140960795 + 471063 * 2 ^ 59
def prefixEnd_471063 : Nat := 4983230072969 + 3 ^ 40 * 471063 * 2
def baseEnd_471063 : Nat := 241881737548995697546127

theorem tailTrace_471063 : CollatzResearch.WordTrace tailWord_471063 prefixEnd_471063 241881737548995697546127 := by
  unfold tailWord_471063
  simp only [CollatzResearch.WordTrace]
  refine ⟨17181079092426677000465843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11454052728284451333643895 17181079092426677000465843)
  ·
    refine ⟨25771618638640015500698765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17181079092426677000465843 25771618638640015500698765)
    ·
      refine ⟨9664356989490005812762037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25771618638640015500698765 9664356989490005812762037)
      ·
        refine ⟨906033467764688044946441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9664356989490005812762037 906033467764688044946441)
        ·
          refine ⟨679525100823516033709831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906033467764688044946441 679525100823516033709831)
          ·
            refine ⟨1019287651235274050564747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679525100823516033709831 1019287651235274050564747)
            ·
              refine ⟨1528931476852911075847121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019287651235274050564747 1528931476852911075847121)
              ·
                refine ⟨1146698607639683306885341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1528931476852911075847121 1146698607639683306885341)
                ·
                  refine ⟨430011977864881240082003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146698607639683306885341 430011977864881240082003)
                  ·
                    refine ⟨645017966797321860123005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 430011977864881240082003 645017966797321860123005)
                    ·
                      refine ⟨241881737548995697546127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 645017966797321860123005 241881737548995697546127)
                      ·
                        rfl

theorem cell23_471063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_471063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471063 prefixEnd_471063 := by exact prefixLift 471063
  have htrace : WordTrace (prefixWord ++ tailWord_471063) baseStart_471063 baseEnd_471063 := by
    simpa [prefixWord, tailWord_471063, baseEnd_471063] using wordTrace_append hprefix tailTrace_471063
  have hstable : (prefixWord ++ tailWord_471063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471063).length < 2 ^ (prefixWord ++ tailWord_471063).sum := by decide
  have hdescent : baseEnd_471063 < baseStart_471063 := by decide
  rcases family_descends (prefixWord ++ tailWord_471063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471096 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 4, 4]
def baseStart_471096 : Nat := 118140960795 + 471096 * 2 ^ 59
def prefixEnd_471096 : Nat := 4983230072969 + 3 ^ 40 * 471096 * 2
def baseEnd_471096 : Nat := 80632894136864689477825

theorem tailTrace_471096 : CollatzResearch.WordTrace tailWord_471096 prefixEnd_471096 80632894136864689477825 := by
  unfold tailWord_471096
  simp only [CollatzResearch.WordTrace]
  refine ⟨8591141350653561818208571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11454855134204749090944761 8591141350653561818208571)
  ·
    refine ⟨12886712025980342727312857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8591141350653561818208571 12886712025980342727312857)
    ·
      refine ⟨9665034019485257045484643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12886712025980342727312857 9665034019485257045484643)
      ·
        refine ⟨14497551029227885568226965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9665034019485257045484643 14497551029227885568226965)
        ·
          refine ⟨679572704495057136010639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14497551029227885568226965 679572704495057136010639)
          ·
            refine ⟨1019359056742585704015959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679572704495057136010639 1019359056742585704015959)
            ·
              refine ⟨1529038585113878556023939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019359056742585704015959 1529038585113878556023939)
              ·
                refine ⟨2293557877670817834035909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1529038585113878556023939 2293557877670817834035909)
                ·
                  refine ⟨430042102063278343881733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2293557877670817834035909 430042102063278343881733)
                  ·
                    refine ⟨80632894136864689477825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 430042102063278343881733 80632894136864689477825)
                    ·
                      rfl

theorem cell23_471096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_471096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471096 prefixEnd_471096 := by exact prefixLift 471096
  have htrace : WordTrace (prefixWord ++ tailWord_471096) baseStart_471096 baseEnd_471096 := by
    simpa [prefixWord, tailWord_471096, baseEnd_471096] using wordTrace_append hprefix tailTrace_471096
  have hstable : (prefixWord ++ tailWord_471096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471096).length < 2 ^ (prefixWord ++ tailWord_471096).sum := by decide
  have hdescent : baseEnd_471096 < baseStart_471096 := by decide
  rcases family_descends (prefixWord ++ tailWord_471096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471112 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_471112 : Nat := 118140960795 + 471112 * 2 ^ 59
def prefixEnd_471112 : Nat := 4983230072969 + 3 ^ 40 * 471112 * 2
def baseEnd_471112 : Nat := 241906898101066005833401

theorem tailTrace_471112 : CollatzResearch.WordTrace tailWord_471112 prefixEnd_471112 241906898101066005833401 := by
  unfold tailWord_471112
  simp only [CollatzResearch.WordTrace]
  refine ⟨8591433134624579184499795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11455244179499438912666393 8591433134624579184499795)
  ·
    refine ⟨12887149701936868776749693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8591433134624579184499795 12887149701936868776749693)
    ·
      refine ⟨4832681138226325791281135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12887149701936868776749693 4832681138226325791281135)
      ·
        refine ⟨7249021707339488686921703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4832681138226325791281135 7249021707339488686921703)
        ·
          refine ⟨10873532561009233030382555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7249021707339488686921703 10873532561009233030382555)
          ·
            refine ⟨16310298841513849545573833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10873532561009233030382555 16310298841513849545573833)
            ·
              refine ⟨12232724131135387159180375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16310298841513849545573833 12232724131135387159180375)
              ·
                refine ⟨18349086196703080738770563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12232724131135387159180375 18349086196703080738770563)
                ·
                  refine ⟨27523629295054621108155845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18349086196703080738770563 27523629295054621108155845)
                  ·
                    refine ⟨5160680492822741457779221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27523629295054621108155845 5160680492822741457779221)
                    ·
                      refine ⟨241906898101066005833401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5160680492822741457779221 241906898101066005833401)
                      ·
                        rfl

theorem cell23_471112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_471112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471112 prefixEnd_471112 := by exact prefixLift 471112
  have htrace : WordTrace (prefixWord ++ tailWord_471112) baseStart_471112 baseEnd_471112 := by
    simpa [prefixWord, tailWord_471112, baseEnd_471112] using wordTrace_append hprefix tailTrace_471112
  have hstable : (prefixWord ++ tailWord_471112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471112).length < 2 ^ (prefixWord ++ tailWord_471112).sum := by decide
  have hdescent : baseEnd_471112 < baseStart_471112 := by decide
  rcases family_descends (prefixWord ++ tailWord_471112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471136 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 4, 1, 3]
def baseStart_471136 : Nat := 118140960795 + 471136 * 2 ^ 59
def prefixEnd_471136 : Nat := 4983230072969 + 3 ^ 40 * 471136 * 2
def baseEnd_471136 : Nat := 241919221636773911933291

theorem tailTrace_471136 : CollatzResearch.WordTrace tailWord_471136 prefixEnd_471136 241919221636773911933291 := by
  unfold tailWord_471136
  simp only [CollatzResearch.WordTrace]
  refine ⟨8591870810581105233936631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11455827747441473645248841 8591870810581105233936631)
  ·
    refine ⟨12887806215871657850904947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8591870810581105233936631 12887806215871657850904947)
    ·
      refine ⟨19331709323807486776357421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12887806215871657850904947 19331709323807486776357421)
      ·
        refine ⟨7249390996427807541134033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19331709323807486776357421 7249390996427807541134033)
        ·
          refine ⟨5437043247320855655850525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7249390996427807541134033 5437043247320855655850525)
          ·
            refine ⟨2038891217745320870943947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5437043247320855655850525 2038891217745320870943947)
            ·
              refine ⟨3058336826617981306415921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2038891217745320870943947 3058336826617981306415921)
              ·
                refine ⟨2293752619963485979811941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3058336826617981306415921 2293752619963485979811941)
                ·
                  refine ⟨430078616243153621214739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2293752619963485979811941 430078616243153621214739)
                  ·
                    refine ⟨645117924364730431822109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 430078616243153621214739 645117924364730431822109)
                    ·
                      refine ⟨241919221636773911933291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 645117924364730431822109 241919221636773911933291)
                      ·
                        rfl

theorem cell23_471136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_471136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471136 prefixEnd_471136 := by exact prefixLift 471136
  have htrace : WordTrace (prefixWord ++ tailWord_471136) baseStart_471136 baseEnd_471136 := by
    simpa [prefixWord, tailWord_471136, baseEnd_471136] using wordTrace_append hprefix tailTrace_471136
  have hstable : (prefixWord ++ tailWord_471136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471136).length < 2 ^ (prefixWord ++ tailWord_471136).sum := by decide
  have hdescent : baseEnd_471136 < baseStart_471136 := by decide
  rcases family_descends (prefixWord ++ tailWord_471136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471149 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_471149 : Nat := 118140960795 + 471149 * 2 ^ 59
def prefixEnd_471149 : Nat := 4983230072969 + 3 ^ 40 * 471149 * 2
def baseEnd_471149 : Nat := 241925896885282361070731

theorem tailTrace_471149 : CollatzResearch.WordTrace tailWord_471149 prefixEnd_471149 241925896885282361070731 := by
  unfold tailWord_471149
  simp only [CollatzResearch.WordTrace]
  refine ⟨17184215770115113688096501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11456143846743409125397667 17184215770115113688096501)
  ·
    refine ⟨1611020228448291908259047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17184215770115113688096501 1611020228448291908259047)
    ·
      refine ⟨2416530342672437862388571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1611020228448291908259047 2416530342672437862388571)
      ·
        refine ⟨3624795514008656793582857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2416530342672437862388571 3624795514008656793582857)
        ·
          refine ⟨2718596635506492595187143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3624795514008656793582857 2718596635506492595187143)
          ·
            refine ⟨4077894953259738892780715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2718596635506492595187143 4077894953259738892780715)
            ·
              refine ⟨6116842429889608339171073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4077894953259738892780715 6116842429889608339171073)
              ·
                refine ⟨4587631822417206254378305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6116842429889608339171073 4587631822417206254378305)
                ·
                  refine ⟨3440723866812904690783729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4587631822417206254378305 3440723866812904690783729)
                  ·
                    refine ⟨2580542900109678518087797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3440723866812904690783729 2580542900109678518087797)
                    ·
                      refine ⟨241925896885282361070731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2580542900109678518087797 241925896885282361070731)
                      ·
                        rfl

theorem cell23_471149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_471149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471149 prefixEnd_471149 := by exact prefixLift 471149
  have htrace : WordTrace (prefixWord ++ tailWord_471149) baseStart_471149 baseEnd_471149 := by
    simpa [prefixWord, tailWord_471149, baseEnd_471149] using wordTrace_append hprefix tailTrace_471149
  have hstable : (prefixWord ++ tailWord_471149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471149).length < 2 ^ (prefixWord ++ tailWord_471149).sum := by decide
  have hdescent : baseEnd_471149 < baseStart_471149 := by decide
  rcases family_descends (prefixWord ++ tailWord_471149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471229 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 1, 7]
def baseStart_471229 : Nat := 118140960795 + 471229 * 2 ^ 59
def prefixEnd_471229 : Nat := 4983230072969 + 3 ^ 40 * 471229 * 2
def baseEnd_471229 : Nat := 80655658445880682690121

theorem tailTrace_471229 : CollatzResearch.WordTrace tailWord_471229 prefixEnd_471229 80655658445880682690121 := by
  unfold tailWord_471229
  simp only [CollatzResearch.WordTrace]
  refine ⟨17187133609825287351008741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11458089073216858234005827 17187133609825287351008741)
  ·
    refine ⟨3222587551842241378314139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17187133609825287351008741 3222587551842241378314139)
    ·
      refine ⟨4833881327763362067471209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3222587551842241378314139 4833881327763362067471209)
      ·
        refine ⟨3625410995822521550603407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4833881327763362067471209 3625410995822521550603407)
        ·
          refine ⟨5438116493733782325905111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3625410995822521550603407 5438116493733782325905111)
          ·
            refine ⟨8157174740600673488857667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5438116493733782325905111 8157174740600673488857667)
            ·
              refine ⟨12235762110901010233286501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8157174740600673488857667 12235762110901010233286501)
              ·
                refine ⟨2294205395793939418741219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12235762110901010233286501 2294205395793939418741219)
                ·
                  refine ⟨3441308093690909128111829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2294205395793939418741219 3441308093690909128111829)
                  ·
                    refine ⟨80655658445880682690121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3441308093690909128111829 80655658445880682690121)
                    ·
                      rfl

theorem cell23_471229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_471229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471229 prefixEnd_471229 := by exact prefixLift 471229
  have htrace : WordTrace (prefixWord ++ tailWord_471229) baseStart_471229 baseEnd_471229 := by
    simpa [prefixWord, tailWord_471229, baseEnd_471229] using wordTrace_append hprefix tailTrace_471229
  have hstable : (prefixWord ++ tailWord_471229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471229).length < 2 ^ (prefixWord ++ tailWord_471229).sum := by decide
  have hdescent : baseEnd_471229 < baseStart_471229 := by decide
  rcases family_descends (prefixWord ++ tailWord_471229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471233 : List Nat := [1, 2, 6, 1, 2, 1, 1, 2, 7]
def baseStart_471233 : Nat := 118140960795 + 471233 * 2 ^ 59
def prefixEnd_471233 : Nat := 4983230072969 + 3 ^ 40 * 471233 * 2
def baseEnd_471233 : Nat := 26885447695584448046705

theorem tailTrace_471233 : CollatzResearch.WordTrace tailWord_471233 prefixEnd_471233 26885447695584448046705 := by
  unfold tailWord_471233
  simp only [CollatzResearch.WordTrace]
  refine ⟨17187279501810796034154353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11458186334540530689436235 17187279501810796034154353)
  ·
    refine ⟨12890459626358097025615765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17187279501810796034154353 12890459626358097025615765)
    ·
      refine ⟨604240294985535798075739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12890459626358097025615765 604240294985535798075739)
      ·
        refine ⟨906360442478303697113609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604240294985535798075739 906360442478303697113609)
        ·
          refine ⟨679770331858727772835207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906360442478303697113609 679770331858727772835207)
          ·
            refine ⟨1019655497788091659252811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679770331858727772835207 1019655497788091659252811)
            ·
              refine ⟨1529483246682137488879217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019655497788091659252811 1529483246682137488879217)
              ·
                refine ⟨1147112435011603116659413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1529483246682137488879217 1147112435011603116659413)
                ·
                  refine ⟨26885447695584448046705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1147112435011603116659413 26885447695584448046705)
                  ·
                    rfl

theorem cell23_471233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 7].length) (baseStart_471233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471233 prefixEnd_471233 := by exact prefixLift 471233
  have htrace : WordTrace (prefixWord ++ tailWord_471233) baseStart_471233 baseEnd_471233 := by
    simpa [prefixWord, tailWord_471233, baseEnd_471233] using wordTrace_append hprefix tailTrace_471233
  have hstable : (prefixWord ++ tailWord_471233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471233).length < 2 ^ (prefixWord ++ tailWord_471233).sum := by decide
  have hdescent : baseEnd_471233 < baseStart_471233 := by decide
  rcases family_descends (prefixWord ++ tailWord_471233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471246 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 1, 7]
def baseStart_471246 : Nat := 118140960795 + 471246 * 2 ^ 59
def prefixEnd_471246 : Nat := 4983230072969 + 3 ^ 40 * 471246 * 2
def baseEnd_471246 : Nat := 80658568169589493852595

theorem tailTrace_471246 : CollatzResearch.WordTrace tailWord_471246 prefixEnd_471246 80658568169589493852595 := by
  unfold tailWord_471246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2148469206345462406797199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11458502433842466169585061 2148469206345462406797199)
  ·
    refine ⟨3222703809518193610195799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2148469206345462406797199 3222703809518193610195799)
    ·
      refine ⟨4834055714277290415293699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3222703809518193610195799 4834055714277290415293699)
      ·
        refine ⟨7251083571415935622940549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4834055714277290415293699 7251083571415935622940549)
        ·
          refine ⟨1359578169640487929301353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7251083571415935622940549 1359578169640487929301353)
          ·
            refine ⟨1019683627230365946976015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1359578169640487929301353 1019683627230365946976015)
            ·
              refine ⟨1529525440845548920464023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019683627230365946976015 1529525440845548920464023)
              ·
                refine ⟨2294288161268323380696035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1529525440845548920464023 2294288161268323380696035)
                ·
                  refine ⟨3441432241902485071044053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2294288161268323380696035 3441432241902485071044053)
                  ·
                    refine ⟨80658568169589493852595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3441432241902485071044053 80658568169589493852595)
                    ·
                      rfl

theorem cell23_471246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_471246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471246 prefixEnd_471246 := by exact prefixLift 471246
  have htrace : WordTrace (prefixWord ++ tailWord_471246) baseStart_471246 baseEnd_471246 := by
    simpa [prefixWord, tailWord_471246, baseEnd_471246] using wordTrace_append hprefix tailTrace_471246
  have hstable : (prefixWord ++ tailWord_471246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471246).length < 2 ^ (prefixWord ++ tailWord_471246).sum := by decide
  have hdescent : baseEnd_471246 < baseStart_471246 := by decide
  rcases family_descends (prefixWord ++ tailWord_471246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471327 : List Nat := [1, 1, 2, 4, 3, 2, 3, 2, 1, 4]
def baseStart_471327 : Nat := 118140960795 + 471327 * 2 ^ 59
def prefixEnd_471327 : Nat := 4983230072969 + 3 ^ 40 * 471327 * 2
def baseEnd_471327 : Nat := 80672432147260888214971

theorem tailTrace_471327 : CollatzResearch.WordTrace tailWord_471327 prefixEnd_471327 80672432147260888214971 := by
  unfold tailWord_471327
  simp only [CollatzResearch.WordTrace]
  refine ⟨17190707963470250088076235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11460471975646833392050823 17190707963470250088076235)
  ·
    refine ⟨25786061945205375132114353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17190707963470250088076235 25786061945205375132114353)
    ·
      refine ⟨19339546458904031349085765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25786061945205375132114353 19339546458904031349085765)
      ·
        refine ⟨3626164961044505877953581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19339546458904031349085765 3626164961044505877953581)
        ·
          refine ⟨1359811860391689704232593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3626164961044505877953581 1359811860391689704232593)
          ·
            refine ⟨1019858895293767278174445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1359811860391689704232593 1019858895293767278174445)
            ·
              refine ⟨382447085735162729315417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1019858895293767278174445 382447085735162729315417)
              ·
                refine ⟨286835314301372046986563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382447085735162729315417 286835314301372046986563)
                ·
                  refine ⟨430252971452058070479845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 286835314301372046986563 430252971452058070479845)
                  ·
                    refine ⟨80672432147260888214971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 430252971452058070479845 80672432147260888214971)
                    ·
                      rfl

theorem cell23_471327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 1, 4].length) (baseStart_471327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471327 prefixEnd_471327 := by exact prefixLift 471327
  have htrace : WordTrace (prefixWord ++ tailWord_471327) baseStart_471327 baseEnd_471327 := by
    simpa [prefixWord, tailWord_471327, baseEnd_471327] using wordTrace_append hprefix tailTrace_471327
  have hstable : (prefixWord ++ tailWord_471327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471327).length < 2 ^ (prefixWord ++ tailWord_471327).sum := by decide
  have hdescent : baseEnd_471327 < baseStart_471327 := by decide
  rcases family_descends (prefixWord ++ tailWord_471327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471353 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 3, 5]
def baseStart_471353 : Nat := 118140960795 + 471353 * 2 ^ 59
def prefixEnd_471353 : Nat := 4983230072969 + 3 ^ 40 * 471353 * 2
def baseEnd_471353 : Nat := 80676882312933187639931

theorem tailTrace_471353 : CollatzResearch.WordTrace tailWord_471353 prefixEnd_471353 80676882312933187639931 := by
  unfold tailWord_471353
  simp only [CollatzResearch.WordTrace]
  refine ⟨17191656261376056528522713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11461104174250704352348475 17191656261376056528522713)
  ·
    refine ⟨12893742196032042396392035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17191656261376056528522713 12893742196032042396392035)
    ·
      refine ⟨19340613294048063594588053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12893742196032042396392035 19340613294048063594588053)
      ·
        refine ⟨906591248158502980996315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19340613294048063594588053 906591248158502980996315)
        ·
          refine ⟨1359886872237754471494473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906591248158502980996315 1359886872237754471494473)
          ·
            refine ⟨1019915154178315853620855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1359886872237754471494473 1019915154178315853620855)
            ·
              refine ⟨1529872731267473780431283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019915154178315853620855 1529872731267473780431283)
              ·
                refine ⟨2294809096901210670646925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1529872731267473780431283 2294809096901210670646925)
                ·
                  refine ⟨860553411337954001492597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2294809096901210670646925 860553411337954001492597)
                  ·
                    refine ⟨80676882312933187639931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 860553411337954001492597 80676882312933187639931)
                    ·
                      rfl

theorem cell23_471353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 5].length) (baseStart_471353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471353 prefixEnd_471353 := by exact prefixLift 471353
  have htrace : WordTrace (prefixWord ++ tailWord_471353) baseStart_471353 baseEnd_471353 := by
    simpa [prefixWord, tailWord_471353, baseEnd_471353] using wordTrace_append hprefix tailTrace_471353
  have hstable : (prefixWord ++ tailWord_471353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471353).length < 2 ^ (prefixWord ++ tailWord_471353).sum := by decide
  have hdescent : baseEnd_471353 < baseStart_471353 := by decide
  rcases family_descends (prefixWord ++ tailWord_471353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471386 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4]
def baseStart_471386 : Nat := 118140960795 + 471386 * 2 ^ 59
def prefixEnd_471386 : Nat := 4983230072969 + 3 ^ 40 * 471386 * 2
def baseEnd_471386 : Nat := 242047591800397933807141

theorem tailTrace_471386 : CollatzResearch.WordTrace tailWord_471386 prefixEnd_471386 242047591800397933807141 := by
  unfold tailWord_471386
  simp only [CollatzResearch.WordTrace]
  refine ⟨4298214967564125791118503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11461906580171002109649341 4298214967564125791118503)
  ·
    refine ⟨6447322451346188686677755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4298214967564125791118503 6447322451346188686677755)
    ·
      refine ⟨9670983677019283030016633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6447322451346188686677755 9670983677019283030016633)
      ·
        refine ⟨7253237757764462272512475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9670983677019283030016633 7253237757764462272512475)
        ·
          refine ⟨10879856636646693408768713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7253237757764462272512475 10879856636646693408768713)
          ·
            refine ⟨8159892477485020056576535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10879856636646693408768713 8159892477485020056576535)
            ·
              refine ⟨12239838716227530084864803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8159892477485020056576535 12239838716227530084864803)
              ·
                refine ⟨18359758074341295127297205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12239838716227530084864803 18359758074341295127297205)
                ·
                  refine ⟨1721227319469496418184113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18359758074341295127297205 1721227319469496418184113)
                  ·
                    refine ⟨1290920489602122313638085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1721227319469496418184113 1290920489602122313638085)
                    ·
                      refine ⟨242047591800397933807141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1290920489602122313638085 242047591800397933807141)
                      ·
                        rfl

theorem cell23_471386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_471386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471386 prefixEnd_471386 := by exact prefixLift 471386
  have htrace : WordTrace (prefixWord ++ tailWord_471386) baseStart_471386 baseEnd_471386 := by
    simpa [prefixWord, tailWord_471386, baseEnd_471386] using wordTrace_append hprefix tailTrace_471386
  have hstable : (prefixWord ++ tailWord_471386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471386).length < 2 ^ (prefixWord ++ tailWord_471386).sum := by decide
  have hdescent : baseEnd_471386 < baseStart_471386 := by decide
  rcases family_descends (prefixWord ++ tailWord_471386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471400 : List Nat := [2, 1, 4, 2, 2, 1, 2, 3, 2, 4]
def baseStart_471400 : Nat := 118140960795 + 471400 * 2 ^ 59
def prefixEnd_471400 : Nat := 4983230072969 + 3 ^ 40 * 471400 * 2
def baseEnd_471400 : Nat := 80684926843186959677359

theorem tailTrace_471400 : CollatzResearch.WordTrace tailWord_471400 prefixEnd_471400 80684926843186959677359 := by
  unfold tailWord_471400
  simp only [CollatzResearch.WordTrace]
  refine ⟨8596685246102891777741827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11462246994803855703655769 8596685246102891777741827)
  ·
    refine ⟨12895027869154337666612741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8596685246102891777741827 12895027869154337666612741)
    ·
      refine ⟨2417817725466438312489889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12895027869154337666612741 2417817725466438312489889)
      ·
        refine ⟨1813363294099828734367417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2417817725466438312489889 1813363294099828734367417)
        ·
          refine ⟨1360022470574871550775563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1813363294099828734367417 1360022470574871550775563)
          ·
            refine ⟨2040033705862307326163345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1360022470574871550775563 2040033705862307326163345)
            ·
              refine ⟨1530025279396730494622509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2040033705862307326163345 1530025279396730494622509)
              ·
                refine ⟨573759479773773935483441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1530025279396730494622509 573759479773773935483441)
                ·
                  refine ⟨430319609830330451612581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573759479773773935483441 430319609830330451612581)
                  ·
                    refine ⟨80684926843186959677359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 430319609830330451612581 80684926843186959677359)
                    ·
                      rfl

theorem cell23_471400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_471400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471400 prefixEnd_471400 := by exact prefixLift 471400
  have htrace : WordTrace (prefixWord ++ tailWord_471400) baseStart_471400 baseEnd_471400 := by
    simpa [prefixWord, tailWord_471400, baseEnd_471400] using wordTrace_append hprefix tailTrace_471400
  have hstable : (prefixWord ++ tailWord_471400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471400).length < 2 ^ (prefixWord ++ tailWord_471400).sum := by decide
  have hdescent : baseEnd_471400 < baseStart_471400 := by decide
  rcases family_descends (prefixWord ++ tailWord_471400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471423 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 6, 1, 3]
def baseStart_471423 : Nat := 118140960795 + 471423 * 2 ^ 59
def prefixEnd_471423 : Nat := 4983230072969 + 3 ^ 40 * 471423 * 2
def baseEnd_471423 : Nat := 242066590584614289044471

theorem tailTrace_471423 : CollatzResearch.WordTrace tailWord_471423 prefixEnd_471423 242066590584614289044471 := by
  unfold tailWord_471423
  simp only [CollatzResearch.WordTrace]
  refine ⟨17194209371122458483570923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11462806247414972322380615 17194209371122458483570923)
  ·
    refine ⟨25791314056683687725356385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17194209371122458483570923 25791314056683687725356385)
    ·
      refine ⟨19343485542512765794017289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25791314056683687725356385 19343485542512765794017289)
      ·
        refine ⟨14507614156884574345512967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19343485542512765794017289 14507614156884574345512967)
        ·
          refine ⟨21761421235326861518269451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14507614156884574345512967 21761421235326861518269451)
          ·
            refine ⟨32642131852990292277404177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21761421235326861518269451 32642131852990292277404177)
            ·
              refine ⟨24481598889742719208053133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32642131852990292277404177 24481598889742719208053133)
              ·
                refine ⟨9180599583653519703019925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24481598889742719208053133 9180599583653519703019925)
                ·
                  refine ⟨430340605483758736079059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9180599583653519703019925 430340605483758736079059)
                  ·
                    refine ⟨645510908225638104118589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 430340605483758736079059 645510908225638104118589)
                    ·
                      refine ⟨242066590584614289044471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 645510908225638104118589 242066590584614289044471)
                      ·
                        rfl

theorem cell23_471423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 1, 3].length) (baseStart_471423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471423 prefixEnd_471423 := by exact prefixLift 471423
  have htrace : WordTrace (prefixWord ++ tailWord_471423) baseStart_471423 baseEnd_471423 := by
    simpa [prefixWord, tailWord_471423, baseEnd_471423] using wordTrace_append hprefix tailTrace_471423
  have hstable : (prefixWord ++ tailWord_471423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471423).length < 2 ^ (prefixWord ++ tailWord_471423).sum := by decide
  have hdescent : baseEnd_471423 < baseStart_471423 := by decide
  rcases family_descends (prefixWord ++ tailWord_471423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471434 : List Nat := [3, 1, 2, 5, 1, 2, 1, 2, 2, 4]
def baseStart_471434 : Nat := 118140960795 + 471434 * 2 ^ 59
def prefixEnd_471434 : Nat := 4983230072969 + 3 ^ 40 * 471434 * 2
def baseEnd_471434 : Nat := 80690746290604582002307

theorem tailTrace_471434 : CollatzResearch.WordTrace tailWord_471434 prefixEnd_471434 80690746290604582002307 := by
  unfold tailWord_471434
  simp only [CollatzResearch.WordTrace]
  refine ⟨4298652643520651840555339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11463073716055071574814237 4298652643520651840555339)
  ·
    refine ⟨6447978965280977760833009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4298652643520651840555339 6447978965280977760833009)
    ·
      refine ⟨4835984223960733320624757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6447978965280977760833009 4835984223960733320624757)
      ·
        refine ⟨453373520996318748808571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4835984223960733320624757 453373520996318748808571)
        ·
          refine ⟨680060281494478123212857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453373520996318748808571 680060281494478123212857)
          ·
            refine ⟨510045211120858592409643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 680060281494478123212857 510045211120858592409643)
            ·
              refine ⟨765067816681287888614465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510045211120858592409643 765067816681287888614465)
              ·
                refine ⟨573800862510965916460849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 765067816681287888614465 573800862510965916460849)
                ·
                  refine ⟨430350646883224437345637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573800862510965916460849 430350646883224437345637)
                  ·
                    refine ⟨80690746290604582002307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 430350646883224437345637 80690746290604582002307)
                    ·
                      rfl

theorem cell23_471434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_471434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471434 prefixEnd_471434 := by exact prefixLift 471434
  have htrace : WordTrace (prefixWord ++ tailWord_471434) baseStart_471434 baseEnd_471434 := by
    simpa [prefixWord, tailWord_471434, baseEnd_471434] using wordTrace_append hprefix tailTrace_471434
  have hstable : (prefixWord ++ tailWord_471434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471434).length < 2 ^ (prefixWord ++ tailWord_471434).sum := by decide
  have hdescent : baseEnd_471434 < baseStart_471434 := by decide
  rcases family_descends (prefixWord ++ tailWord_471434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471510 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_471510 : Nat := 118140960795 + 471510 * 2 ^ 59
def prefixEnd_471510 : Nat := 4983230072969 + 3 ^ 40 * 471510 * 2
def baseEnd_471510 : Nat := 242111263401555448656571

theorem tailTrace_471510 : CollatzResearch.WordTrace tailWord_471510 prefixEnd_471510 242111263401555448656571 := by
  unfold tailWord_471510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1074836407612954521374249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11464921681204848227991989 1074836407612954521374249)
  ·
    refine ⟨806127305709715891030687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1074836407612954521374249 806127305709715891030687)
    ·
      refine ⟨1209190958564573836546031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 806127305709715891030687 1209190958564573836546031)
      ·
        refine ⟨1813786437846860754819047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209190958564573836546031 1813786437846860754819047)
        ·
          refine ⟨2720679656770291132228571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1813786437846860754819047 2720679656770291132228571)
          ·
            refine ⟨4081019485155436698342857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2720679656770291132228571 4081019485155436698342857)
            ·
              refine ⟨3060764613866577523757143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4081019485155436698342857 3060764613866577523757143)
              ·
                refine ⟨4591146920799866285635715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3060764613866577523757143 4591146920799866285635715)
                ·
                  refine ⟨6886720381199799428453573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4591146920799866285635715 6886720381199799428453573)
                  ·
                    refine ⟨1291260071474962392835045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6886720381199799428453573 1291260071474962392835045)
                    ·
                      refine ⟨242111263401555448656571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1291260071474962392835045 242111263401555448656571)
                      ·
                        rfl

theorem cell23_471510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_471510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471510 prefixEnd_471510 := by exact prefixLift 471510
  have htrace : WordTrace (prefixWord ++ tailWord_471510) baseStart_471510 baseEnd_471510 := by
    simpa [prefixWord, tailWord_471510, baseEnd_471510] using wordTrace_append hprefix tailTrace_471510
  have hstable : (prefixWord ++ tailWord_471510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471510).length < 2 ^ (prefixWord ++ tailWord_471510).sum := by decide
  have hdescent : baseEnd_471510 < baseStart_471510 := by decide
  rcases family_descends (prefixWord ++ tailWord_471510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471513 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 1, 5, 3]
def baseStart_471513 : Nat := 118140960795 + 471513 * 2 ^ 59
def prefixEnd_471513 : Nat := 4983230072969 + 3 ^ 40 * 471513 * 2
def baseEnd_471513 : Nat := 242112803843518936919057

theorem tailTrace_471513 : CollatzResearch.WordTrace tailWord_471513 prefixEnd_471513 242112803843518936919057 := by
  unfold tailWord_471513
  simp only [CollatzResearch.WordTrace]
  refine ⟨17197491940796403854347193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11464994627197602569564795 17197491940796403854347193)
  ·
    refine ⟨12898118955597302890760395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17197491940796403854347193 12898118955597302890760395)
    ·
      refine ⟨19347178433395954336140593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12898118955597302890760395 19347178433395954336140593)
      ·
        refine ⟨14510383825046965752105445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19347178433395954336140593 14510383825046965752105445)
        ·
          refine ⟨2720696967196306078519771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14510383825046965752105445 2720696967196306078519771)
          ·
            refine ⟨4081045450794459117779657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2720696967196306078519771 4081045450794459117779657)
            ·
              refine ⟨3060784088095844338334743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4081045450794459117779657 3060784088095844338334743)
              ·
                refine ⟨4591176132143766507502115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3060784088095844338334743 4591176132143766507502115)
                ·
                  refine ⟨6886764198215649761253173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4591176132143766507502115 6886764198215649761253173)
                  ·
                    refine ⟨645634143582717165117485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6886764198215649761253173 645634143582717165117485)
                    ·
                      refine ⟨242112803843518936919057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 645634143582717165117485 242112803843518936919057)
                      ·
                        rfl

theorem cell23_471513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_471513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471513 prefixEnd_471513 := by exact prefixLift 471513
  have htrace : WordTrace (prefixWord ++ tailWord_471513) baseStart_471513 baseEnd_471513 := by
    simpa [prefixWord, tailWord_471513, baseEnd_471513] using wordTrace_append hprefix tailTrace_471513
  have hstable : (prefixWord ++ tailWord_471513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471513).length < 2 ^ (prefixWord ++ tailWord_471513).sum := by decide
  have hdescent : baseEnd_471513 < baseStart_471513 := by decide
  rcases family_descends (prefixWord ++ tailWord_471513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471554 : List Nat := [3, 4, 1, 2, 2, 1, 1, 4, 5]
def baseStart_471554 : Nat := 118140960795 + 471554 * 2 ^ 59
def prefixEnd_471554 : Nat := 4983230072969 + 3 ^ 40 * 471554 * 2
def baseEnd_471554 : Nat := 26903761838928141834041

theorem tailTrace_471554 : CollatzResearch.WordTrace tailWord_471554 prefixEnd_471554 26903761838928141834041 := by
  unfold tailWord_471554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4299746833411966964147429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11465991555765245237726477 4299746833411966964147429)
  ·
    refine ⟨806202531264743805777643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4299746833411966964147429 806202531264743805777643)
    ·
      refine ⟨1209303796897115708666465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 806202531264743805777643 1209303796897115708666465)
      ·
        refine ⟨906977847672836781499849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1209303796897115708666465 906977847672836781499849)
        ·
          refine ⟨680233385754627586124887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906977847672836781499849 680233385754627586124887)
          ·
            refine ⟨1020350078631941379187331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680233385754627586124887 1020350078631941379187331)
            ·
              refine ⟨1530525117947912068780997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020350078631941379187331 1530525117947912068780997)
              ·
                refine ⟨286973459615233512896437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1530525117947912068780997 286973459615233512896437)
                ·
                  refine ⟨26903761838928141834041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 286973459615233512896437 26903761838928141834041)
                  ·
                    rfl

theorem cell23_471554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_471554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471554 prefixEnd_471554 := by exact prefixLift 471554
  have htrace : WordTrace (prefixWord ++ tailWord_471554) baseStart_471554 baseEnd_471554 := by
    simpa [prefixWord, tailWord_471554, baseEnd_471554] using wordTrace_append hprefix tailTrace_471554
  have hstable : (prefixWord ++ tailWord_471554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471554).length < 2 ^ (prefixWord ++ tailWord_471554).sum := by decide
  have hdescent : baseEnd_471554 < baseStart_471554 := by decide
  rcases family_descends (prefixWord ++ tailWord_471554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471580 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 5, 4]
def baseStart_471580 : Nat := 118140960795 + 471580 * 2 ^ 59
def prefixEnd_471580 : Nat := 4983230072969 + 3 ^ 40 * 471580 * 2
def baseEnd_471580 : Nat := 80715735682456724927083

theorem tailTrace_471580 : CollatzResearch.WordTrace tailWord_471580 prefixEnd_471580 80715735682456724927083 := by
  unfold tailWord_471580
  simp only [CollatzResearch.WordTrace]
  refine ⟨8599967815776837148518097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11466623754369116198024129 8599967815776837148518097)
  ·
    refine ⟨6449975861832627861388573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8599967815776837148518097 6449975861832627861388573)
    ·
      refine ⟨2418740948187235448020715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6449975861832627861388573 2418740948187235448020715)
      ·
        refine ⟨3628111422280853172031073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2418740948187235448020715 3628111422280853172031073)
        ·
          refine ⟨2721083566710639879023305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3628111422280853172031073 2721083566710639879023305)
          ·
            refine ⟨2040812675032979909267479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2721083566710639879023305 2040812675032979909267479)
            ·
              refine ⟨3061219012549469863901219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2040812675032979909267479 3061219012549469863901219)
              ·
                refine ⟨4591828518824204795851829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3061219012549469863901219 4591828518824204795851829)
                ·
                  refine ⟨430483923639769199611109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4591828518824204795851829 430483923639769199611109)
                  ·
                    refine ⟨80715735682456724927083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 430483923639769199611109 80715735682456724927083)
                    ·
                      rfl

theorem cell23_471580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_471580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471580 prefixEnd_471580 := by exact prefixLift 471580
  have htrace : WordTrace (prefixWord ++ tailWord_471580) baseStart_471580 baseEnd_471580 := by
    simpa [prefixWord, tailWord_471580, baseEnd_471580] using wordTrace_append hprefix tailTrace_471580
  have hstable : (prefixWord ++ tailWord_471580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471580).length < 2 ^ (prefixWord ++ tailWord_471580).sum := by decide
  have hdescent : baseEnd_471580 < baseStart_471580 := by decide
  rcases family_descends (prefixWord ++ tailWord_471580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471584 : List Nat := [2, 1, 1, 6, 3, 1, 1, 1, 2, 5]
def baseStart_471584 : Nat := 118140960795 + 471584 * 2 ^ 59
def prefixEnd_471584 : Nat := 4983230072969 + 3 ^ 40 * 471584 * 2
def baseEnd_471584 : Nat := 80716420323329386377077

theorem tailTrace_471584 : CollatzResearch.WordTrace tailWord_471584 prefixEnd_471584 80716420323329386377077 := by
  unfold tailWord_471584
  simp only [CollatzResearch.WordTrace]
  refine ⟨8600040761769591490090903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11466721015692788653454537 8600040761769591490090903)
  ·
    refine ⟨12900061142654387235136355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8600040761769591490090903 12900061142654387235136355)
    ·
      refine ⟨19350091713981580852704533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12900061142654387235136355 19350091713981580852704533)
      ·
        refine ⟨907035549092886602470525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19350091713981580852704533 907035549092886602470525)
        ·
          refine ⟨340138330909832475926447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 907035549092886602470525 340138330909832475926447)
          ·
            refine ⟨510207496364748713889671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340138330909832475926447 510207496364748713889671)
            ·
              refine ⟨765311244547123070834507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510207496364748713889671 765311244547123070834507)
              ·
                refine ⟨1147966866820684606251761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765311244547123070834507 1147966866820684606251761)
                ·
                  refine ⟨860975150115513454688821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1147966866820684606251761 860975150115513454688821)
                  ·
                    refine ⟨80716420323329386377077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 860975150115513454688821 80716420323329386377077)
                    ·
                      rfl

theorem cell23_471584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 2, 5].length) (baseStart_471584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471584 prefixEnd_471584 := by exact prefixLift 471584
  have htrace : WordTrace (prefixWord ++ tailWord_471584) baseStart_471584 baseEnd_471584 := by
    simpa [prefixWord, tailWord_471584, baseEnd_471584] using wordTrace_append hprefix tailTrace_471584
  have hstable : (prefixWord ++ tailWord_471584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471584).length < 2 ^ (prefixWord ++ tailWord_471584).sum := by decide
  have hdescent : baseEnd_471584 < baseStart_471584 := by decide
  rcases family_descends (prefixWord ++ tailWord_471584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471587 : List Nat := [1, 1, 1, 4, 4, 3, 1, 1, 2, 1, 4]
def baseStart_471587 : Nat := 118140960795 + 471587 * 2 ^ 59
def prefixEnd_471587 : Nat := 4983230072969 + 3 ^ 40 * 471587 * 2
def baseEnd_471587 : Nat := 242150801411951647393717

theorem tailTrace_471587 : CollatzResearch.WordTrace tailWord_471587 prefixEnd_471587 242150801411951647393717 := by
  unfold tailWord_471587
  simp only [CollatzResearch.WordTrace]
  refine ⟨17200190942528314492541015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11466793961685542995027343 17200190942528314492541015)
  ·
    refine ⟨25800286413792471738811523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17200190942528314492541015 25800286413792471738811523)
    ·
      refine ⟨38700429620688707608217285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25800286413792471738811523 38700429620688707608217285)
      ·
        refine ⟨7256330553879132676540741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38700429620688707608217285 7256330553879132676540741)
        ·
          refine ⟨1360561978852337376851389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7256330553879132676540741 1360561978852337376851389)
          ·
            refine ⟨510210742069626516319271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1360561978852337376851389 510210742069626516319271)
            ·
              refine ⟨765316113104439774478907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510210742069626516319271 765316113104439774478907)
              ·
                refine ⟨1147974169656659661718361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765316113104439774478907 1147974169656659661718361)
                ·
                  refine ⟨860980627242494746288771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1147974169656659661718361 860980627242494746288771)
                  ·
                    refine ⟨1291470940863742119433157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 860980627242494746288771 1291470940863742119433157)
                    ·
                      refine ⟨242150801411951647393717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1291470940863742119433157 242150801411951647393717)
                      ·
                        rfl

theorem cell23_471587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_471587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471587 prefixEnd_471587 := by exact prefixLift 471587
  have htrace : WordTrace (prefixWord ++ tailWord_471587) baseStart_471587 baseEnd_471587 := by
    simpa [prefixWord, tailWord_471587, baseEnd_471587] using wordTrace_append hprefix tailTrace_471587
  have hstable : (prefixWord ++ tailWord_471587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471587).length < 2 ^ (prefixWord ++ tailWord_471587).sum := by decide
  have hdescent : baseEnd_471587 < baseStart_471587 := by decide
  rcases family_descends (prefixWord ++ tailWord_471587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471610 : List Nat := [3, 1, 1, 1, 3, 3, 3, 2, 6]
def baseStart_471610 : Nat := 118140960795 + 471610 * 2 ^ 59
def prefixEnd_471610 : Nat := 4983230072969 + 3 ^ 40 * 471610 * 2
def baseEnd_471610 : Nat := 26906956829667228600679

theorem tailTrace_471610 : CollatzResearch.WordTrace tailWord_471610 prefixEnd_471610 26906956829667228600679 := by
  unfold tailWord_471610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4300257455361247355157071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11467353214296659613752189 4300257455361247355157071)
  ·
    refine ⟨6450386183041871032735607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4300257455361247355157071 6450386183041871032735607)
    ·
      refine ⟨9675579274562806549103411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6450386183041871032735607 9675579274562806549103411)
      ·
        refine ⟨14513368911844209823655117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9675579274562806549103411 14513368911844209823655117)
        ·
          refine ⟨5442513341941578683870669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14513368911844209823655117 5442513341941578683870669)
          ·
            refine ⟨2040942503228092006451501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5442513341941578683870669 2040942503228092006451501)
            ·
              refine ⟨765353438710534502419313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2040942503228092006451501 765353438710534502419313)
              ·
                refine ⟨574015079032900876814485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 765353438710534502419313 574015079032900876814485)
                ·
                  refine ⟨26906956829667228600679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 574015079032900876814485 26906956829667228600679)
                  ·
                    rfl

theorem cell23_471610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 6].length) (baseStart_471610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471610 prefixEnd_471610 := by exact prefixLift 471610
  have htrace : WordTrace (prefixWord ++ tailWord_471610) baseStart_471610 baseEnd_471610 := by
    simpa [prefixWord, tailWord_471610, baseEnd_471610] using wordTrace_append hprefix tailTrace_471610
  have hstable : (prefixWord ++ tailWord_471610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471610).length < 2 ^ (prefixWord ++ tailWord_471610).sum := by decide
  have hdescent : baseEnd_471610 < baseStart_471610 := by decide
  rcases family_descends (prefixWord ++ tailWord_471610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471637 : List Nat := [1, 3, 2, 2, 1, 1, 4, 2, 3, 1, 3]
def baseStart_471637 : Nat := 118140960795 + 471637 * 2 ^ 59
def prefixEnd_471637 : Nat := 4983230072969 + 3 ^ 40 * 471637 * 2
def baseEnd_471637 : Nat := 242176475444676451768487

theorem tailTrace_471637 : CollatzResearch.WordTrace tailWord_471637 prefixEnd_471637 242176475444676451768487 := by
  unfold tailWord_471637
  simp only [CollatzResearch.WordTrace]
  refine ⟨17202014592347173031861165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11468009728231448687907443 17202014592347173031861165)
  ·
    refine ⟨6450755472130189886947937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17202014592347173031861165 6450755472130189886947937)
    ·
      refine ⟨4838066604097642415210953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6450755472130189886947937 4838066604097642415210953)
      ·
        refine ⟨3628549953073231811408215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4838066604097642415210953 3628549953073231811408215)
        ·
          refine ⟨5442824929609847717112323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3628549953073231811408215 5442824929609847717112323)
          ·
            refine ⟨8164237394414771575668485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5442824929609847717112323 8164237394414771575668485)
            ·
              refine ⟨1530794511452769670437841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8164237394414771575668485 1530794511452769670437841)
              ·
                refine ⟨1148095883589577252828381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1530794511452769670437841 1148095883589577252828381)
                ·
                  refine ⟨430535956346091469810643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148095883589577252828381 430535956346091469810643)
                  ·
                    refine ⟨645803934519137204715965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 430535956346091469810643 645803934519137204715965)
                    ·
                      refine ⟨242176475444676451768487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 645803934519137204715965 242176475444676451768487)
                      ·
                        rfl

theorem cell23_471637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_471637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471637 prefixEnd_471637 := by exact prefixLift 471637
  have htrace : WordTrace (prefixWord ++ tailWord_471637) baseStart_471637 baseEnd_471637 := by
    simpa [prefixWord, tailWord_471637, baseEnd_471637] using wordTrace_append hprefix tailTrace_471637
  have hstable : (prefixWord ++ tailWord_471637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471637).length < 2 ^ (prefixWord ++ tailWord_471637).sum := by decide
  have hdescent : baseEnd_471637 < baseStart_471637 := by decide
  rcases family_descends (prefixWord ++ tailWord_471637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471640 : List Nat := [2, 1, 2, 2, 1, 2, 3, 4, 1, 5]
def baseStart_471640 : Nat := 118140960795 + 471640 * 2 ^ 59
def prefixEnd_471640 : Nat := 4983230072969 + 3 ^ 40 * 471640 * 2
def baseEnd_471640 : Nat := 80726005295546646676991

theorem tailTrace_471640 : CollatzResearch.WordTrace tailWord_471640 prefixEnd_471640 80726005295546646676991 := by
  unfold tailWord_471640
  simp only [CollatzResearch.WordTrace]
  refine ⟨8601062005668152272110187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11468082674224203029480249 8601062005668152272110187)
  ·
    refine ⟨12901593008502228408165281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8601062005668152272110187 12901593008502228408165281)
    ·
      refine ⟨9676194756376671306123961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12901593008502228408165281 9676194756376671306123961)
      ·
        refine ⟨7257146067282503479592971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9676194756376671306123961 7257146067282503479592971)
        ·
          refine ⟨10885719100923755219389457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7257146067282503479592971 10885719100923755219389457)
          ·
            refine ⟨8164289325692816414542093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10885719100923755219389457 8164289325692816414542093)
            ·
              refine ⟨3061608497134806155453285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8164289325692816414542093 3061608497134806155453285)
              ·
                refine ⟨574051593212776154147491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3061608497134806155453285 574051593212776154147491)
                ·
                  refine ⟨861077389819164231221237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574051593212776154147491 861077389819164231221237)
                  ·
                    refine ⟨80726005295546646676991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 861077389819164231221237 80726005295546646676991)
                    ·
                      rfl

theorem cell23_471640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_471640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471640 prefixEnd_471640 := by exact prefixLift 471640
  have htrace : WordTrace (prefixWord ++ tailWord_471640) baseStart_471640 baseEnd_471640 := by
    simpa [prefixWord, tailWord_471640, baseEnd_471640] using wordTrace_append hprefix tailTrace_471640
  have hstable : (prefixWord ++ tailWord_471640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471640).length < 2 ^ (prefixWord ++ tailWord_471640).sum := by decide
  have hdescent : baseEnd_471640 < baseStart_471640 := by decide
  rcases family_descends (prefixWord ++ tailWord_471640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471664 : List Nat := [2, 1, 1, 1, 7, 1, 1, 2, 2, 3, 2]
def baseStart_471664 : Nat := 118140960795 + 471664 * 2 ^ 59
def prefixEnd_471664 : Nat := 4983230072969 + 3 ^ 40 * 471664 * 2
def baseEnd_471664 : Nat := 242190339422347846130863

theorem tailTrace_471664 : CollatzResearch.WordTrace tailWord_471664 prefixEnd_471664 242190339422347846130863 := by
  unfold tailWord_471664
  simp only [CollatzResearch.WordTrace]
  refine ⟨8601499681624678321547023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11468666242166237762062697 8601499681624678321547023)
  ·
    refine ⟨12902249522437017482320535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8601499681624678321547023 12902249522437017482320535)
    ·
      refine ⟨19353374283655526223480803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12902249522437017482320535 19353374283655526223480803)
      ·
        refine ⟨29030061425483289335221205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19353374283655526223480803 29030061425483289335221205)
        ·
          refine ⟨680392064659764593794247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 29030061425483289335221205 680392064659764593794247)
          ·
            refine ⟨1020588096989646890691371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680392064659764593794247 1020588096989646890691371)
            ·
              refine ⟨1530882145484470336037057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020588096989646890691371 1530882145484470336037057)
              ·
                refine ⟨1148161609113352752027793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1530882145484470336037057 1148161609113352752027793)
                ·
                  refine ⟨861121206835014564020845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1148161609113352752027793 861121206835014564020845)
                  ·
                    refine ⟨322920452563130461507817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 861121206835014564020845 322920452563130461507817)
                    ·
                      refine ⟨242190339422347846130863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 322920452563130461507817 242190339422347846130863)
                      ·
                        rfl

theorem cell23_471664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 2, 3, 2].length) (baseStart_471664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471664 prefixEnd_471664 := by exact prefixLift 471664
  have htrace : WordTrace (prefixWord ++ tailWord_471664) baseStart_471664 baseEnd_471664 := by
    simpa [prefixWord, tailWord_471664, baseEnd_471664] using wordTrace_append hprefix tailTrace_471664
  have hstable : (prefixWord ++ tailWord_471664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471664).length < 2 ^ (prefixWord ++ tailWord_471664).sum := by decide
  have hdescent : baseEnd_471664 < baseStart_471664 := by decide
  rcases family_descends (prefixWord ++ tailWord_471664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471680 : List Nat := [2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 5]
def baseStart_471680 : Nat := 118140960795 + 471680 * 2 ^ 59
def prefixEnd_471680 : Nat := 4983230072969 + 3 ^ 40 * 471680 * 2
def baseEnd_471680 : Nat := 242198555112819783530789

theorem tailTrace_471680 : CollatzResearch.WordTrace tailWord_471680 prefixEnd_471680 242198555112819783530789 := by
  unfold tailWord_471680
  simp only [CollatzResearch.WordTrace]
  refine ⟨8601791465595695687838247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11469055287460927583784329 8601791465595695687838247)
  ·
    refine ⟨12902687198393543531757371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8601791465595695687838247 12902687198393543531757371)
    ·
      refine ⟨19354030797590315297636057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12902687198393543531757371 19354030797590315297636057)
      ·
        refine ⟨14515523098192736473227043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19354030797590315297636057 14515523098192736473227043)
        ·
          refine ⟨21773284647289104709840565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14515523098192736473227043 21773284647289104709840565)
          ·
            refine ⟨2041245435683353566547553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21773284647289104709840565 2041245435683353566547553)
            ·
              refine ⟨1530934076762515174910665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2041245435683353566547553 1530934076762515174910665)
              ·
                refine ⟨1148200557571886381182999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1530934076762515174910665 1148200557571886381182999)
                ·
                  refine ⟨1722300836357829571774499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1148200557571886381182999 1722300836357829571774499)
                  ·
                    refine ⟨2583451254536744357661749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1722300836357829571774499 2583451254536744357661749)
                    ·
                      refine ⟨242198555112819783530789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2583451254536744357661749 242198555112819783530789)
                      ·
                        rfl

theorem cell23_471680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_471680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471680 prefixEnd_471680 := by exact prefixLift 471680
  have htrace : WordTrace (prefixWord ++ tailWord_471680) baseStart_471680 baseEnd_471680 := by
    simpa [prefixWord, tailWord_471680, baseEnd_471680] using wordTrace_append hprefix tailTrace_471680
  have hstable : (prefixWord ++ tailWord_471680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471680).length < 2 ^ (prefixWord ++ tailWord_471680).sum := by decide
  have hdescent : baseEnd_471680 < baseStart_471680 := by decide
  rcases family_descends (prefixWord ++ tailWord_471680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471683 : List Nat := [1, 1, 1, 3, 3, 1, 3, 10]
def baseStart_471683 : Nat := 118140960795 + 471683 * 2 ^ 59
def prefixEnd_471683 : Nat := 4983230072969 + 3 ^ 40 * 471683 * 2
def baseEnd_471683 : Nat := 8970373909436417473825

theorem tailTrace_471683 : CollatzResearch.WordTrace tailWord_471683 prefixEnd_471683 8970373909436417473825 := by
  unfold tailWord_471683
  simp only [CollatzResearch.WordTrace]
  refine ⟨17203692350180522888035703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11469128233453681925357135 17203692350180522888035703)
  ·
    refine ⟨25805538525270784332053555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17203692350180522888035703 25805538525270784332053555)
    ·
      refine ⟨38708307787906176498080333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25805538525270784332053555 38708307787906176498080333)
      ·
        refine ⟨14515615420464816186780125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38708307787906176498080333 14515615420464816186780125)
        ·
          refine ⟨5443355782674306070042547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14515615420464816186780125 5443355782674306070042547)
          ·
            refine ⟨8165033674011459105063821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5443355782674306070042547 8165033674011459105063821)
            ·
              refine ⟨3061887627754297164398933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8165033674011459105063821 3061887627754297164398933)
              ·
                refine ⟨8970373909436417473825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3061887627754297164398933 8970373909436417473825)
                ·
                  rfl

theorem cell23_471683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 10].length) (baseStart_471683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471683 prefixEnd_471683 := by exact prefixLift 471683
  have htrace : WordTrace (prefixWord ++ tailWord_471683) baseStart_471683 baseEnd_471683 := by
    simpa [prefixWord, tailWord_471683, baseEnd_471683] using wordTrace_append hprefix tailTrace_471683
  have hstable : (prefixWord ++ tailWord_471683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471683).length < 2 ^ (prefixWord ++ tailWord_471683).sum := by decide
  have hdescent : baseEnd_471683 < baseStart_471683 := by decide
  rcases family_descends (prefixWord ++ tailWord_471683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471687 : List Nat := [1, 1, 4, 2, 1, 2, 3, 3, 2, 4]
def baseStart_471687 : Nat := 118140960795 + 471687 * 2 ^ 59
def prefixEnd_471687 : Nat := 4983230072969 + 3 ^ 40 * 471687 * 2
def baseEnd_471687 : Nat := 80734049825800418714419

theorem tailTrace_471687 : CollatzResearch.WordTrace tailWord_471687 prefixEnd_471687 80734049825800418714419 := by
  unfold tailWord_471687
  simp only [CollatzResearch.WordTrace]
  refine ⟨17203838242166031571181315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11469225494777354380787543 17203838242166031571181315)
  ·
    refine ⟨25805757363249047356771973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17203838242166031571181315 25805757363249047356771973)
    ·
      refine ⟨4838579505609196379394745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25805757363249047356771973 4838579505609196379394745)
      ·
        refine ⟨3628934629206897284546059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4838579505609196379394745 3628934629206897284546059)
        ·
          refine ⟨5443401943810345926819089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3628934629206897284546059 5443401943810345926819089)
          ·
            refine ⟨4082551457857759445114317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5443401943810345926819089 4082551457857759445114317)
            ·
              refine ⟨1530956796696659791917869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4082551457857759445114317 1530956796696659791917869)
              ·
                refine ⟨574108798761247421969201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1530956796696659791917869 574108798761247421969201)
                ·
                  refine ⟨430581599070935566476901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574108798761247421969201 430581599070935566476901)
                  ·
                    refine ⟨80734049825800418714419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 430581599070935566476901 80734049825800418714419)
                    ·
                      rfl

theorem cell23_471687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_471687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471687 prefixEnd_471687 := by exact prefixLift 471687
  have htrace : WordTrace (prefixWord ++ tailWord_471687) baseStart_471687 baseEnd_471687 := by
    simpa [prefixWord, tailWord_471687, baseEnd_471687] using wordTrace_append hprefix tailTrace_471687
  have hstable : (prefixWord ++ tailWord_471687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471687).length < 2 ^ (prefixWord ++ tailWord_471687).sum := by decide
  have hdescent : baseEnd_471687 < baseStart_471687 := by decide
  rcases family_descends (prefixWord ++ tailWord_471687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471694 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2]
def baseStart_471694 : Nat := 118140960795 + 471694 * 2 ^ 59
def prefixEnd_471694 : Nat := 4983230072969 + 3 ^ 40 * 471694 * 2
def baseEnd_471694 : Nat := 242205743841982728755725

theorem tailTrace_471694 : CollatzResearch.WordTrace tailWord_471694 prefixEnd_471694 242205743841982728755725 := by
  unfold tailWord_471694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2150511694142583970835767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11469395702093781177790757 2150511694142583970835767)
  ·
    refine ⟨3225767541213875956253651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2150511694142583970835767 3225767541213875956253651)
    ·
      refine ⟨4838651311820813934380477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3225767541213875956253651 4838651311820813934380477)
      ·
        refine ⟨1814494241932805225392679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4838651311820813934380477 1814494241932805225392679)
        ·
          refine ⟨2721741362899207838089019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814494241932805225392679 2721741362899207838089019)
          ·
            refine ⟨4082612044348811757133529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721741362899207838089019 4082612044348811757133529)
            ·
              refine ⟨3061959033261608817850147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4082612044348811757133529 3061959033261608817850147)
              ·
                refine ⟨4592938549892413226775221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3061959033261608817850147 4592938549892413226775221)
                ·
                  refine ⟨430587989052413740010177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4592938549892413226775221 430587989052413740010177)
                  ·
                    refine ⟨322940991789310305007633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 430587989052413740010177 322940991789310305007633)
                    ·
                      refine ⟨242205743841982728755725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 322940991789310305007633 242205743841982728755725)
                      ·
                        rfl

theorem cell23_471694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_471694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471694 prefixEnd_471694 := by exact prefixLift 471694
  have htrace : WordTrace (prefixWord ++ tailWord_471694) baseStart_471694 baseEnd_471694 := by
    simpa [prefixWord, tailWord_471694, baseEnd_471694] using wordTrace_append hprefix tailTrace_471694
  have hstable : (prefixWord ++ tailWord_471694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471694).length < 2 ^ (prefixWord ++ tailWord_471694).sum := by decide
  have hdescent : baseEnd_471694 < baseStart_471694 := by decide
  rcases family_descends (prefixWord ++ tailWord_471694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471722 : List Nat := [3, 1, 5, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_471722 : Nat := 118140960795 + 471722 * 2 ^ 59
def prefixEnd_471722 : Nat := 4983230072969 + 3 ^ 40 * 471722 * 2
def baseEnd_471722 : Nat := 242220121300308619205597

theorem tailTrace_471722 : CollatzResearch.WordTrace tailWord_471722 prefixEnd_471722 242220121300308619205597 := by
  unfold tailWord_471722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4301278699259808137176355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11470076531359488365803613 4301278699259808137176355)
  ·
    refine ⟨6451918048889712205764533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4301278699259808137176355 6451918048889712205764533)
    ·
      refine ⟨604867317083410519290425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6451918048889712205764533 604867317083410519290425)
      ·
        refine ⟨453650487812557889467819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 604867317083410519290425 453650487812557889467819)
        ·
          refine ⟨680475731718836834201729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453650487812557889467819 680475731718836834201729)
          ·
            refine ⟨510356798789127625651297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 680475731718836834201729 510356798789127625651297)
            ·
              refine ⟨382767599091845719238473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510356798789127625651297 382767599091845719238473)
              ·
                refine ⟨287075699318884289428855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382767599091845719238473 287075699318884289428855)
                ·
                  refine ⟨430613548978326434143283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287075699318884289428855 430613548978326434143283)
                  ·
                    refine ⟨645920323467489651214925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 430613548978326434143283 645920323467489651214925)
                    ·
                      refine ⟨242220121300308619205597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 645920323467489651214925 242220121300308619205597)
                      ·
                        rfl

theorem cell23_471722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_471722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471722 prefixEnd_471722 := by exact prefixLift 471722
  have htrace : WordTrace (prefixWord ++ tailWord_471722) baseStart_471722 baseEnd_471722 := by
    simpa [prefixWord, tailWord_471722, baseEnd_471722] using wordTrace_append hprefix tailTrace_471722
  have hstable : (prefixWord ++ tailWord_471722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471722).length < 2 ^ (prefixWord ++ tailWord_471722).sum := by decide
  have hdescent : baseEnd_471722 < baseStart_471722 := by decide
  rcases family_descends (prefixWord ++ tailWord_471722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471744 : List Nat := [2, 1, 1, 2, 4, 2, 2, 3, 2, 1, 3]
def baseStart_471744 : Nat := 118140960795 + 471744 * 2 ^ 59
def prefixEnd_471744 : Nat := 4983230072969 + 3 ^ 40 * 471744 * 2
def baseEnd_471744 : Nat := 242231417874707533130495

theorem tailTrace_471744 : CollatzResearch.WordTrace tailWord_471744 prefixEnd_471744 242231417874707533130495 := by
  unfold tailWord_471744
  simp only [CollatzResearch.WordTrace]
  refine ⟨8602958601479765153003143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11470611468639686870670857 8602958601479765153003143)
  ·
    refine ⟨12904437902219647729504715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8602958601479765153003143 12904437902219647729504715)
    ·
      refine ⟨19356656853329471594257073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12904437902219647729504715 19356656853329471594257073)
      ·
        refine ⟨14517492639997103695692805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19356656853329471594257073 14517492639997103695692805)
        ·
          refine ⟨2722029869999456942942401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14517492639997103695692805 2722029869999456942942401)
          ·
            refine ⟨2041522402499592707206801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2722029869999456942942401 2041522402499592707206801)
            ·
              refine ⟨1531141801874694530405101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2041522402499592707206801 1531141801874694530405101)
              ·
                refine ⟨574178175703010448901913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1531141801874694530405101 574178175703010448901913)
                ·
                  refine ⟨430633631777257836676435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574178175703010448901913 430633631777257836676435)
                  ·
                    refine ⟨645950447665886755014653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 430633631777257836676435 645950447665886755014653)
                    ·
                      refine ⟨242231417874707533130495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 645950447665886755014653 242231417874707533130495)
                      ·
                        rfl

theorem cell23_471744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 2, 1, 3].length) (baseStart_471744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471744 prefixEnd_471744 := by exact prefixLift 471744
  have htrace : WordTrace (prefixWord ++ tailWord_471744) baseStart_471744 baseEnd_471744 := by
    simpa [prefixWord, tailWord_471744, baseEnd_471744] using wordTrace_append hprefix tailTrace_471744
  have hstable : (prefixWord ++ tailWord_471744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471744).length < 2 ^ (prefixWord ++ tailWord_471744).sum := by decide
  have hdescent : baseEnd_471744 < baseStart_471744 := by decide
  rcases family_descends (prefixWord ++ tailWord_471744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471754 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 3, 3, 2]
def baseStart_471754 : Nat := 118140960795 + 471754 * 2 ^ 59
def prefixEnd_471754 : Nat := 4983230072969 + 3 ^ 40 * 471754 * 2
def baseEnd_471754 : Nat := 242236552681252494005449

theorem tailTrace_471754 : CollatzResearch.WordTrace tailWord_471754 prefixEnd_471754 242236552681252494005449 := by
  unfold tailWord_471754
  simp only [CollatzResearch.WordTrace]
  refine ⟨4301570483230825503467579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11470854621948868009246877 4301570483230825503467579)
  ·
    refine ⟨6452355724846238255201369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4301570483230825503467579 6452355724846238255201369)
    ·
      refine ⟨4839266793634678691401027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6452355724846238255201369 4839266793634678691401027)
      ·
        refine ⟨7258900190452018037101541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4839266793634678691401027 7258900190452018037101541)
        ·
          refine ⟨1361043785709753381956539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7258900190452018037101541 1361043785709753381956539)
          ·
            refine ⟨2041565678564630072934809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361043785709753381956539 2041565678564630072934809)
            ·
              refine ⟨1531174258923472554701107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2041565678564630072934809 1531174258923472554701107)
              ·
                refine ⟨2296761388385208832051661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1531174258923472554701107 2296761388385208832051661)
                ·
                  refine ⟨861285520644453312019373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2296761388385208832051661 861285520644453312019373)
                  ·
                    refine ⟨322982070241669992007265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 861285520644453312019373 322982070241669992007265)
                    ·
                      refine ⟨242236552681252494005449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 322982070241669992007265 242236552681252494005449)
                      ·
                        rfl

theorem cell23_471754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_471754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471754 prefixEnd_471754 := by exact prefixLift 471754
  have htrace : WordTrace (prefixWord ++ tailWord_471754) baseStart_471754 baseEnd_471754 := by
    simpa [prefixWord, tailWord_471754, baseEnd_471754] using wordTrace_append hprefix tailTrace_471754
  have hstable : (prefixWord ++ tailWord_471754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471754).length < 2 ^ (prefixWord ++ tailWord_471754).sum := by decide
  have hdescent : baseEnd_471754 < baseStart_471754 := by decide
  rcases family_descends (prefixWord ++ tailWord_471754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471765 : List Nat := [1, 3, 2, 5, 2, 1, 2, 1, 1, 2, 3]
def baseStart_471765 : Nat := 118140960795 + 471765 * 2 ^ 59
def prefixEnd_471765 : Nat := 4983230072969 + 3 ^ 40 * 471765 * 2
def baseEnd_471765 : Nat := 242242200968451950967899

theorem tailTrace_471765 : CollatzResearch.WordTrace tailWord_471765 prefixEnd_471765 242242200968451950967899 := by
  unfold tailWord_471765
  simp only [CollatzResearch.WordTrace]
  refine ⟨17206683135883450892520749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11471122090588967261680499 17206683135883450892520749)
  ·
    refine ⟨6452506175956294084695281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17206683135883450892520749 6452506175956294084695281)
    ·
      refine ⟨4839379631967220563521461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6452506175956294084695281 4839379631967220563521461)
      ·
        refine ⟨453691840496926927830137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4839379631967220563521461 453691840496926927830137)
        ·
          refine ⟨340268880372695195872603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453691840496926927830137 340268880372695195872603)
          ·
            refine ⟨510403320559042793808905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340268880372695195872603 510403320559042793808905)
            ·
              refine ⟨382802490419282095356679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510403320559042793808905 382802490419282095356679)
              ·
                refine ⟨574203735628923143035019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382802490419282095356679 574203735628923143035019)
                ·
                  refine ⟨861305603443384714552529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574203735628923143035019 861305603443384714552529)
                  ·
                    refine ⟨645979202582538535914397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 861305603443384714552529 645979202582538535914397)
                    ·
                      refine ⟨242242200968451950967899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 645979202582538535914397 242242200968451950967899)
                      ·
                        rfl

theorem cell23_471765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_471765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471765 prefixEnd_471765 := by exact prefixLift 471765
  have htrace : WordTrace (prefixWord ++ tailWord_471765) baseStart_471765 baseEnd_471765 := by
    simpa [prefixWord, tailWord_471765, baseEnd_471765] using wordTrace_append hprefix tailTrace_471765
  have hstable : (prefixWord ++ tailWord_471765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471765).length < 2 ^ (prefixWord ++ tailWord_471765).sum := by decide
  have hdescent : baseEnd_471765 < baseStart_471765 := by decide
  rcases family_descends (prefixWord ++ tailWord_471765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471770 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5]
def baseStart_471770 : Nat := 118140960795 + 471770 * 2 ^ 59
def prefixEnd_471770 : Nat := 4983230072969 + 3 ^ 40 * 471770 * 2
def baseEnd_471770 : Nat := 242244768371724431405375

theorem tailTrace_471770 : CollatzResearch.WordTrace tailWord_471770 prefixEnd_471770 242244768371724431405375 := by
  unfold tailWord_471770
  simp only [CollatzResearch.WordTrace]
  refine ⟨4301716375216334186613191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11471243667243557830968509 4301716375216334186613191)
  ·
    refine ⟨6452574562824501279919787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4301716375216334186613191 6452574562824501279919787)
    ·
      refine ⟨9678861844236751919879681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6452574562824501279919787 9678861844236751919879681)
      ·
        refine ⟨7259146383177563939909761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9678861844236751919879681 7259146383177563939909761)
        ·
          refine ⟨5444359787383172954932321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7259146383177563939909761 5444359787383172954932321)
          ·
            refine ⟨4083269840537379716199241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5444359787383172954932321 4083269840537379716199241)
            ·
              refine ⟨3062452380403034787149431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4083269840537379716199241 3062452380403034787149431)
              ·
                refine ⟨4593678570604552180724147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062452380403034787149431 4593678570604552180724147)
                ·
                  refine ⟨6890517855906828271086221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4593678570604552180724147 6890517855906828271086221)
                  ·
                    refine ⟨2583944195965060601657333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6890517855906828271086221 2583944195965060601657333)
                    ·
                      refine ⟨242244768371724431405375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2583944195965060601657333 242244768371724431405375)
                      ·
                        rfl

theorem cell23_471770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_471770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471770 prefixEnd_471770 := by exact prefixLift 471770
  have htrace : WordTrace (prefixWord ++ tailWord_471770) baseStart_471770 baseEnd_471770 := by
    simpa [prefixWord, tailWord_471770, baseEnd_471770] using wordTrace_append hprefix tailTrace_471770
  have hstable : (prefixWord ++ tailWord_471770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471770).length < 2 ^ (prefixWord ++ tailWord_471770).sum := by decide
  have hdescent : baseEnd_471770 < baseStart_471770 := by decide
  rcases family_descends (prefixWord ++ tailWord_471770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471857 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 4, 1, 4]
def baseStart_471857 : Nat := 118140960795 + 471857 * 2 ^ 59
def prefixEnd_471857 : Nat := 4983230072969 + 3 ^ 40 * 471857 * 2
def baseEnd_471857 : Nat := 242289441188665591017475

theorem tailTrace_471857 : CollatzResearch.WordTrace tailWord_471857 prefixEnd_471857 242289441188665591017475 := by
  unfold tailWord_471857
  simp only [CollatzResearch.WordTrace]
  refine ⟨17210038651550150604869825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11473359101033433736579883 17210038651550150604869825)
  ·
    refine ⟨12907528988662612953652369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17210038651550150604869825 12907528988662612953652369)
    ·
      refine ⟨9680646741496959715239277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12907528988662612953652369 9680646741496959715239277)
      ·
        refine ⟨3630242528061359893214729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9680646741496959715239277 3630242528061359893214729)
        ·
          refine ⟨2722681896046019919911047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3630242528061359893214729 2722681896046019919911047)
          ·
            refine ⟨4084022844069029879866571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722681896046019919911047 4084022844069029879866571)
            ·
              refine ⟨6126034266103544819799857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4084022844069029879866571 6126034266103544819799857)
              ·
                refine ⟨4594525699577658614849893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6126034266103544819799857 4594525699577658614849893)
                ·
                  refine ⟨861473568670810990284355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4594525699577658614849893 861473568670810990284355)
                  ·
                    refine ⟨1292210353006216485426533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 861473568670810990284355 1292210353006216485426533)
                    ·
                      refine ⟨242289441188665591017475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1292210353006216485426533 242289441188665591017475)
                      ·
                        rfl

theorem cell23_471857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_471857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471857 prefixEnd_471857 := by exact prefixLift 471857
  have htrace : WordTrace (prefixWord ++ tailWord_471857) baseStart_471857 baseEnd_471857 := by
    simpa [prefixWord, tailWord_471857, baseEnd_471857] using wordTrace_append hprefix tailTrace_471857
  have hstable : (prefixWord ++ tailWord_471857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471857).length < 2 ^ (prefixWord ++ tailWord_471857).sum := by decide
  have hdescent : baseEnd_471857 < baseStart_471857 := by decide
  rcases family_descends (prefixWord ++ tailWord_471857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471897 : List Nat := [1, 2, 1, 2, 2, 4, 1, 4, 6]
def baseStart_471897 : Nat := 118140960795 + 471897 * 2 ^ 59
def prefixEnd_471897 : Nat := 4983230072969 + 3 ^ 40 * 471897 * 2
def baseEnd_471897 : Nat := 26923331157205048279699

theorem tailTrace_471897 : CollatzResearch.WordTrace tailWord_471897 prefixEnd_471897 26923331157205048279699 := by
  unfold tailWord_471897
  simp only [CollatzResearch.WordTrace]
  refine ⟨17211497571405237436325945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11474331714270158290883963 17211497571405237436325945)
  ·
    refine ⟨12908623178553928077244459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17211497571405237436325945 12908623178553928077244459)
    ·
      refine ⟨19362934767830892115866689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12908623178553928077244459 19362934767830892115866689)
      ·
        refine ⟨14522201075873169086900017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19362934767830892115866689 14522201075873169086900017)
        ·
          refine ⟨10891650806904876815175013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14522201075873169086900017 10891650806904876815175013)
          ·
            refine ⟨2042184526294664402845315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10891650806904876815175013 2042184526294664402845315)
            ·
              refine ⟨3063276789441996604267973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2042184526294664402845315 3063276789441996604267973)
              ·
                refine ⟨574364398020374363300245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3063276789441996604267973 574364398020374363300245)
                ·
                  refine ⟨26923331157205048279699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 574364398020374363300245 26923331157205048279699)
                  ·
                    rfl

theorem cell23_471897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 6].length) (baseStart_471897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471897 prefixEnd_471897 := by exact prefixLift 471897
  have htrace : WordTrace (prefixWord ++ tailWord_471897) baseStart_471897 baseEnd_471897 := by
    simpa [prefixWord, tailWord_471897, baseEnd_471897] using wordTrace_append hprefix tailTrace_471897
  have hstable : (prefixWord ++ tailWord_471897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471897).length < 2 ^ (prefixWord ++ tailWord_471897).sum := by decide
  have hdescent : baseEnd_471897 < baseStart_471897 := by decide
  rcases family_descends (prefixWord ++ tailWord_471897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471977 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 1, 1, 6]
def baseStart_471977 : Nat := 118140960795 + 471977 * 2 ^ 59
def prefixEnd_471977 : Nat := 4983230072969 + 3 ^ 40 * 471977 * 2
def baseEnd_471977 : Nat := 242351058867205121516923

theorem tailTrace_471977 : CollatzResearch.WordTrace tailWord_471977 prefixEnd_471977 242351058867205121516923 := by
  unfold tailWord_471977
  simp only [CollatzResearch.WordTrace]
  refine ⟨17214415411115411099238185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11476276940743607399492123 17214415411115411099238185)
  ·
    refine ⟨12910811558336558324428639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17214415411115411099238185 12910811558336558324428639)
    ·
      refine ⟨19366217337504837486642959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12910811558336558324428639 19366217337504837486642959)
      ·
        refine ⟨29049326006257256229964439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19366217337504837486642959 29049326006257256229964439)
        ·
          refine ⟨43573989009385884344946659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29049326006257256229964439 43573989009385884344946659)
          ·
            refine ⟨65360983514078826517419989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43573989009385884344946659 65360983514078826517419989)
            ·
              refine ⟨1531898051111222496502031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 65360983514078826517419989 1531898051111222496502031)
              ·
                refine ⟨2297847076666833744753047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1531898051111222496502031 2297847076666833744753047)
                ·
                  refine ⟨3446770615000250617129571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2297847076666833744753047 3446770615000250617129571)
                  ·
                    refine ⟨5170155922500375925694357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3446770615000250617129571 5170155922500375925694357)
                    ·
                      refine ⟨242351058867205121516923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5170155922500375925694357 242351058867205121516923)
                      ·
                        rfl

theorem cell23_471977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_471977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_471977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_471977 prefixEnd_471977 := by exact prefixLift 471977
  have htrace : WordTrace (prefixWord ++ tailWord_471977) baseStart_471977 baseEnd_471977 := by
    simpa [prefixWord, tailWord_471977, baseEnd_471977] using wordTrace_append hprefix tailTrace_471977
  have hstable : (prefixWord ++ tailWord_471977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471977).length < 2 ^ (prefixWord ++ tailWord_471977).sum := by decide
  have hdescent : baseEnd_471977 < baseStart_471977 := by decide
  rcases family_descends (prefixWord ++ tailWord_471977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472017 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 2, 7]
def baseStart_472017 : Nat := 118140960795 + 472017 * 2 ^ 59
def prefixEnd_472017 : Nat := 4983230072969 + 3 ^ 40 * 472017 * 2
def baseEnd_472017 : Nat := 80790532697794988338913

theorem tailTrace_472017 : CollatzResearch.WordTrace tailWord_472017 prefixEnd_472017 80790532697794988338913 := by
  unfold tailWord_472017
  simp only [CollatzResearch.WordTrace]
  refine ⟨17215874330970497930694305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11477249553980331953796203 17215874330970497930694305)
  ·
    refine ⟨12911905748227873448020729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17215874330970497930694305 12911905748227873448020729)
    ·
      refine ⟨9683929311170905086015547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12911905748227873448020729 9683929311170905086015547)
      ·
        refine ⟨14525893966756357629023321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9683929311170905086015547 14525893966756357629023321)
        ·
          refine ⟨10894420475067268221767491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14525893966756357629023321 10894420475067268221767491)
          ·
            refine ⟨16341630712600902332651237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10894420475067268221767491 16341630712600902332651237)
            ·
              refine ⟨3064055758612669187372107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16341630712600902332651237 3064055758612669187372107)
              ·
                refine ⟨4596083637919003781058161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3064055758612669187372107 4596083637919003781058161)
                ·
                  refine ⟨3447062728439252835793621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4596083637919003781058161 3447062728439252835793621)
                  ·
                    refine ⟨80790532697794988338913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3447062728439252835793621 80790532697794988338913)
                    ·
                      rfl

theorem cell23_472017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_472017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472017 prefixEnd_472017 := by exact prefixLift 472017
  have htrace : WordTrace (prefixWord ++ tailWord_472017) baseStart_472017 baseEnd_472017 := by
    simpa [prefixWord, tailWord_472017, baseEnd_472017] using wordTrace_append hprefix tailTrace_472017
  have hstable : (prefixWord ++ tailWord_472017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472017).length < 2 ^ (prefixWord ++ tailWord_472017).sum := by decide
  have hdescent : baseEnd_472017 < baseStart_472017 := by decide
  rcases family_descends (prefixWord ++ tailWord_472017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472067 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 6]
def baseStart_472067 : Nat := 118140960795 + 472067 * 2 ^ 59
def prefixEnd_472067 : Nat := 4983230072969 + 3 ^ 40 * 472067 * 2
def baseEnd_472067 : Nat := 242397272126109769391509

theorem tailTrace_472067 : CollatzResearch.WordTrace tailWord_472067 prefixEnd_472067 242397272126109769391509 := by
  unfold tailWord_472067
  simp only [CollatzResearch.WordTrace]
  refine ⟨17217697980789356470014455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11478465320526237646676303 17217697980789356470014455)
  ·
    refine ⟨25826546971184034705021683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17217697980789356470014455 25826546971184034705021683)
    ·
      refine ⟨38739820456776052057532525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25826546971184034705021683 38739820456776052057532525)
      ·
        refine ⟨14527432671291019521574697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38739820456776052057532525 14527432671291019521574697)
        ·
          refine ⟨10895574503468264641181023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14527432671291019521574697 10895574503468264641181023)
          ·
            refine ⟨16343361755202396961771535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10895574503468264641181023 16343361755202396961771535)
            ·
              refine ⟨24515042632803595442657303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16343361755202396961771535 24515042632803595442657303)
              ·
                refine ⟨36772563949205393163985955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24515042632803595442657303 36772563949205393163985955)
                ·
                  refine ⟨55158845923808089745978933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36772563949205393163985955 55158845923808089745978933)
                  ·
                    refine ⟨5171141805357008413685525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55158845923808089745978933 5171141805357008413685525)
                    ·
                      refine ⟨242397272126109769391509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5171141805357008413685525 242397272126109769391509)
                      ·
                        rfl

theorem cell23_472067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_472067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472067 prefixEnd_472067 := by exact prefixLift 472067
  have htrace : WordTrace (prefixWord ++ tailWord_472067) baseStart_472067 baseEnd_472067 := by
    simpa [prefixWord, tailWord_472067, baseEnd_472067] using wordTrace_append hprefix tailTrace_472067
  have hstable : (prefixWord ++ tailWord_472067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472067).length < 2 ^ (prefixWord ++ tailWord_472067).sum := by decide
  have hdescent : baseEnd_472067 < baseStart_472067 := by decide
  rcases family_descends (prefixWord ++ tailWord_472067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472071 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 3, 4, 2]
def baseStart_472071 : Nat := 118140960795 + 472071 * 2 ^ 59
def prefixEnd_472071 : Nat := 4983230072969 + 3 ^ 40 * 472071 * 2
def baseEnd_472071 : Nat := 242399326048727753741491

theorem tailTrace_472071 : CollatzResearch.WordTrace tailWord_472071 prefixEnd_472071 242399326048727753741491 := by
  unfold tailWord_472071
  simp only [CollatzResearch.WordTrace]
  refine ⟨17217843872774865153160067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11478562581849910102106711 17217843872774865153160067)
  ·
    refine ⟨25826765809162297729740101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17217843872774865153160067 25826765809162297729740101)
    ·
      refine ⟨4842518589217930824326269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25826765809162297729740101 4842518589217930824326269)
      ·
        refine ⟨1815944470956724059122351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4842518589217930824326269 1815944470956724059122351)
        ·
          refine ⟨2723916706435086088683527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1815944470956724059122351 2723916706435086088683527)
          ·
            refine ⟨4085875059652629133025291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2723916706435086088683527 4085875059652629133025291)
            ·
              refine ⟨6128812589478943699537937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4085875059652629133025291 6128812589478943699537937)
              ·
                refine ⟨4596609442109207774653453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6128812589478943699537937 4596609442109207774653453)
                ·
                  refine ⟨1723728540790952915495045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4596609442109207774653453 1723728540790952915495045)
                  ·
                    refine ⟨323199101398303671655321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1723728540790952915495045 323199101398303671655321)
                    ·
                      refine ⟨242399326048727753741491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 323199101398303671655321 242399326048727753741491)
                      ·
                        rfl

theorem cell23_472071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_472071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472071 prefixEnd_472071 := by exact prefixLift 472071
  have htrace : WordTrace (prefixWord ++ tailWord_472071) baseStart_472071 baseEnd_472071 := by
    simpa [prefixWord, tailWord_472071, baseEnd_472071] using wordTrace_append hprefix tailTrace_472071
  have hstable : (prefixWord ++ tailWord_472071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472071).length < 2 ^ (prefixWord ++ tailWord_472071).sum := by decide
  have hdescent : baseEnd_472071 < baseStart_472071 := by decide
  rcases family_descends (prefixWord ++ tailWord_472071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472082 : List Nat := [3, 2, 5, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_472082 : Nat := 118140960795 + 472082 * 2 ^ 59
def prefixEnd_472082 : Nat := 4983230072969 + 3 ^ 40 * 472082 * 2
def baseEnd_472082 : Nat := 242404974335927210703941

theorem tailTrace_472082 : CollatzResearch.WordTrace tailWord_472082 prefixEnd_472082 242404974335927210703941 := by
  unfold tailWord_472082
  simp only [CollatzResearch.WordTrace]
  refine ⟨4304561268933753507952625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11478830050490009354540333 4304561268933753507952625)
  ·
    refine ⟨3228420951700315130964469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4304561268933753507952625 3228420951700315130964469)
    ·
      refine ⟨302664464221904543527919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3228420951700315130964469 302664464221904543527919)
      ·
        refine ⟨453996696332856815291879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302664464221904543527919 453996696332856815291879)
        ·
          refine ⟨680995044499285222937819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453996696332856815291879 680995044499285222937819)
          ·
            refine ⟨1021492566748927834406729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680995044499285222937819 1021492566748927834406729)
            ·
              refine ⟨766119425061695875805047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1021492566748927834406729 766119425061695875805047)
              ·
                refine ⟨1149179137592543813707571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766119425061695875805047 1149179137592543813707571)
                ·
                  refine ⟨1723768706388815720561357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149179137592543813707571 1723768706388815720561357)
                  ·
                    refine ⟨646413264895805895210509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1723768706388815720561357 646413264895805895210509)
                    ·
                      refine ⟨242404974335927210703941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 646413264895805895210509 242404974335927210703941)
                      ·
                        rfl

theorem cell23_472082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_472082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472082 prefixEnd_472082 := by exact prefixLift 472082
  have htrace : WordTrace (prefixWord ++ tailWord_472082) baseStart_472082 baseEnd_472082 := by
    simpa [prefixWord, tailWord_472082, baseEnd_472082] using wordTrace_append hprefix tailTrace_472082
  have hstable : (prefixWord ++ tailWord_472082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472082).length < 2 ^ (prefixWord ++ tailWord_472082).sum := by decide
  have hdescent : baseEnd_472082 < baseStart_472082 := by decide
  rcases family_descends (prefixWord ++ tailWord_472082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472088 : List Nat := [2, 1, 2, 3, 2, 3, 2, 1, 1, 4, 2]
def baseStart_472088 : Nat := 118140960795 + 472088 * 2 ^ 59
def prefixEnd_472088 : Nat := 4983230072969 + 3 ^ 40 * 472088 * 2
def baseEnd_472088 : Nat := 242408055219854187228913

theorem tailTrace_472088 : CollatzResearch.WordTrace tailWord_472088 prefixEnd_472088 242408055219854187228913 := by
  unfold tailWord_472088
  simp only [CollatzResearch.WordTrace]
  refine ⟨8609231956856638528264459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11478975942475518037685945 8609231956856638528264459)
  ·
    refine ⟨12913847935284957792396689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8609231956856638528264459 12913847935284957792396689)
    ·
      refine ⟨9685385951463718344297517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12913847935284957792396689 9685385951463718344297517)
      ·
        refine ⟨3632019731798894379111569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9685385951463718344297517 3632019731798894379111569)
        ·
          refine ⟨2724014798849170784333677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3632019731798894379111569 2724014798849170784333677)
          ·
            refine ⟨1021505549568439044125129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2724014798849170784333677 1021505549568439044125129)
            ·
              refine ⟨766129162176329283093847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1021505549568439044125129 766129162176329283093847)
              ·
                refine ⟨1149193743264493924640771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766129162176329283093847 1149193743264493924640771)
                ·
                  refine ⟨1723790614896740886961157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149193743264493924640771 1723790614896740886961157)
                  ·
                    refine ⟨323210740293138916305217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1723790614896740886961157 323210740293138916305217)
                    ·
                      refine ⟨242408055219854187228913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 323210740293138916305217 242408055219854187228913)
                      ·
                        rfl

theorem cell23_472088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_472088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472088 prefixEnd_472088 := by exact prefixLift 472088
  have htrace : WordTrace (prefixWord ++ tailWord_472088) baseStart_472088 baseEnd_472088 := by
    simpa [prefixWord, tailWord_472088, baseEnd_472088] using wordTrace_append hprefix tailTrace_472088
  have hstable : (prefixWord ++ tailWord_472088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472088).length < 2 ^ (prefixWord ++ tailWord_472088).sum := by decide
  have hdescent : baseEnd_472088 < baseStart_472088 := by decide
  rcases family_descends (prefixWord ++ tailWord_472088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472121 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 2, 3, 3]
def baseStart_472121 : Nat := 118140960795 + 472121 * 2 ^ 59
def prefixEnd_472121 : Nat := 4983230072969 + 3 ^ 40 * 472121 * 2
def baseEnd_472121 : Nat := 242425000081452558116261

theorem tailTrace_472121 : CollatzResearch.WordTrace tailWord_472121 prefixEnd_472121 242425000081452558116261 := by
  unfold tailWord_472121
  simp only [CollatzResearch.WordTrace]
  refine ⟨17219667522593723692480217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11479778348395815794986811 17219667522593723692480217)
  ·
    refine ⟨12914750641945292769360163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17219667522593723692480217 12914750641945292769360163)
    ·
      refine ⟨19372125962917939154040245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12914750641945292769360163 19372125962917939154040245)
      ·
        refine ⟨1816136809023556795691273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19372125962917939154040245 1816136809023556795691273)
        ·
          refine ⟨1362102606767667596768455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1816136809023556795691273 1362102606767667596768455)
          ·
            refine ⟨2043153910151501395152683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362102606767667596768455 2043153910151501395152683)
            ·
              refine ⟨3064730865227252092729025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043153910151501395152683 3064730865227252092729025)
              ·
                refine ⟨2298548148920439069546769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3064730865227252092729025 2298548148920439069546769)
                ·
                  refine ⟨1723911111690329302160077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2298548148920439069546769 1723911111690329302160077)
                  ·
                    refine ⟨646466666883873488310029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1723911111690329302160077 646466666883873488310029)
                    ·
                      refine ⟨242425000081452558116261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 646466666883873488310029 242425000081452558116261)
                      ·
                        rfl

theorem cell23_472121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_472121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472121 prefixEnd_472121 := by exact prefixLift 472121
  have htrace : WordTrace (prefixWord ++ tailWord_472121) baseStart_472121 baseEnd_472121 := by
    simpa [prefixWord, tailWord_472121, baseEnd_472121] using wordTrace_append hprefix tailTrace_472121
  have hstable : (prefixWord ++ tailWord_472121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472121).length < 2 ^ (prefixWord ++ tailWord_472121).sum := by decide
  have hdescent : baseEnd_472121 < baseStart_472121 := by decide
  rcases family_descends (prefixWord ++ tailWord_472121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472141 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_472141 : Nat := 118140960795 + 472141 * 2 ^ 59
def prefixEnd_472141 : Nat := 4983230072969 + 3 ^ 40 * 472141 * 2
def baseEnd_472141 : Nat := 80811756564847493288723

theorem tailTrace_472141 : CollatzResearch.WordTrace tailWord_472141 prefixEnd_472141 80811756564847493288723 := by
  unfold tailWord_472141
  simp only [CollatzResearch.WordTrace]
  refine ⟨17220396982521267108208277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11480264655014178072138851 17220396982521267108208277)
  ·
    refine ⟨807206108555684395697263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17220396982521267108208277 807206108555684395697263)
    ·
      refine ⟨1210809162833526593545895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 807206108555684395697263 1210809162833526593545895)
      ·
        refine ⟨1816213744250289890318843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1210809162833526593545895 1816213744250289890318843)
        ·
          refine ⟨2724320616375434835478265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1816213744250289890318843 2724320616375434835478265)
          ·
            refine ⟨2043240462281576126608699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2724320616375434835478265 2043240462281576126608699)
            ·
              refine ⟨3064860693422364189913049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043240462281576126608699 3064860693422364189913049)
              ·
                refine ⟨2298645520066773142434787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3064860693422364189913049 2298645520066773142434787)
                ·
                  refine ⟨3447968280100159713652181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2298645520066773142434787 3447968280100159713652181)
                  ·
                    refine ⟨80811756564847493288723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3447968280100159713652181 80811756564847493288723)
                    ·
                      rfl

theorem cell23_472141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_472141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472141 prefixEnd_472141 := by exact prefixLift 472141
  have htrace : WordTrace (prefixWord ++ tailWord_472141) baseStart_472141 baseEnd_472141 := by
    simpa [prefixWord, tailWord_472141, baseEnd_472141] using wordTrace_append hprefix tailTrace_472141
  have hstable : (prefixWord ++ tailWord_472141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472141).length < 2 ^ (prefixWord ++ tailWord_472141).sum := by decide
  have hdescent : baseEnd_472141 < baseStart_472141 := by decide
  rcases family_descends (prefixWord ++ tailWord_472141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472161 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 1, 6, 2]
def baseStart_472161 : Nat := 118140960795 + 472161 * 2 ^ 59
def prefixEnd_472161 : Nat := 4983230072969 + 3 ^ 40 * 472161 * 2
def baseEnd_472161 : Nat := 242445539307632401616077

theorem tailTrace_472161 : CollatzResearch.WordTrace tailWord_472161 prefixEnd_472161 242445539307632401616077 := by
  unfold tailWord_472161
  simp only [CollatzResearch.WordTrace]
  refine ⟨17221126442448810523936337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11480750961632540349290891 17221126442448810523936337)
  ·
    refine ⟨12915844831836607892952253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17221126442448810523936337 12915844831836607892952253)
    ·
      refine ⟨4843441811938727959857095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12915844831836607892952253 4843441811938727959857095)
      ·
        refine ⟨7265162717908091939785643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4843441811938727959857095 7265162717908091939785643)
        ·
          refine ⟨10897744076862137909678465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7265162717908091939785643 10897744076862137909678465)
          ·
            refine ⟨8173308057646603432258849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10897744076862137909678465 8173308057646603432258849)
            ·
              refine ⟨6129981043234952574194137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8173308057646603432258849 6129981043234952574194137)
              ·
                refine ⟨4597485782426214430645603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6129981043234952574194137 4597485782426214430645603)
                ·
                  refine ⟨6896228673639321645968405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4597485782426214430645603 6896228673639321645968405)
                  ·
                    refine ⟨323260719076843202154769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6896228673639321645968405 323260719076843202154769)
                    ·
                      refine ⟨242445539307632401616077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 323260719076843202154769 242445539307632401616077)
                      ·
                        rfl

theorem cell23_472161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_472161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472161 prefixEnd_472161 := by exact prefixLift 472161
  have htrace : WordTrace (prefixWord ++ tailWord_472161) baseStart_472161 baseEnd_472161 := by
    simpa [prefixWord, tailWord_472161, baseEnd_472161] using wordTrace_append hprefix tailTrace_472161
  have hstable : (prefixWord ++ tailWord_472161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472161).length < 2 ^ (prefixWord ++ tailWord_472161).sum := by decide
  have hdescent : baseEnd_472161 < baseStart_472161 := by decide
  rcases family_descends (prefixWord ++ tailWord_472161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472164 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_472164 : Nat := 118140960795 + 472164 * 2 ^ 59
def prefixEnd_472164 : Nat := 4983230072969 + 3 ^ 40 * 472164 * 2
def baseEnd_472164 : Nat := 242447079749595889878563

theorem tailTrace_472164 : CollatzResearch.WordTrace tailWord_472164 prefixEnd_472164 242447079749595889878563 := by
  unfold tailWord_472164
  simp only [CollatzResearch.WordTrace]
  refine ⟨8610617930718971018147773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11480823907625294690863697 8610617930718971018147773)
  ·
    refine ⟨3228981724019614131805415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8610617930718971018147773 3228981724019614131805415)
    ·
      refine ⟨4843472586029421197708123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3228981724019614131805415 4843472586029421197708123)
      ·
        refine ⟨7265208879044131796562185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4843472586029421197708123 7265208879044131796562185)
        ·
          refine ⟨5448906659283098847421639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7265208879044131796562185 5448906659283098847421639)
          ·
            refine ⟨8173359988924648271132459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5448906659283098847421639 8173359988924648271132459)
            ·
              refine ⟨12260039983386972406698689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8173359988924648271132459 12260039983386972406698689)
              ·
                refine ⟨9195029987540229305024017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12260039983386972406698689 9195029987540229305024017)
                ·
                  refine ⟨6896272490655171978768013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9195029987540229305024017 6896272490655171978768013)
                  ·
                    refine ⟨2586102183995689492038005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6896272490655171978768013 2586102183995689492038005)
                    ·
                      refine ⟨242447079749595889878563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2586102183995689492038005 242447079749595889878563)
                      ·
                        rfl

theorem cell23_472164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_472164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472164 prefixEnd_472164 := by exact prefixLift 472164
  have htrace : WordTrace (prefixWord ++ tailWord_472164) baseStart_472164 baseEnd_472164 := by
    simpa [prefixWord, tailWord_472164, baseEnd_472164] using wordTrace_append hprefix tailTrace_472164
  have hstable : (prefixWord ++ tailWord_472164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472164).length < 2 ^ (prefixWord ++ tailWord_472164).sum := by decide
  have hdescent : baseEnd_472164 < baseStart_472164 := by decide
  rcases family_descends (prefixWord ++ tailWord_472164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472184 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 8]
def baseStart_472184 : Nat := 118140960795 + 472184 * 2 ^ 59
def prefixEnd_472184 : Nat := 4983230072969 + 3 ^ 40 * 472184 * 2
def baseEnd_472184 : Nat := 26939705484742867958719

theorem tailTrace_472184 : CollatzResearch.WordTrace tailWord_472184 prefixEnd_472184 26939705484742867958719 := by
  unfold tailWord_472184
  simp only [CollatzResearch.WordTrace]
  refine ⟨8610982660682742726011803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11481310214243656968015737 8610982660682742726011803)
  ·
    refine ⟨12916473991024114089017705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8610982660682742726011803 12916473991024114089017705)
    ·
      refine ⟨9687355493268085566763279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12916473991024114089017705 9687355493268085566763279)
      ·
        refine ⟨14531033239902128350144919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9687355493268085566763279 14531033239902128350144919)
        ·
          refine ⟨21796549859853192525217379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14531033239902128350144919 21796549859853192525217379)
          ·
            refine ⟨32694824789779788787826069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21796549859853192525217379 32694824789779788787826069)
            ·
              refine ⟨1532569912020927599429347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32694824789779788787826069 1532569912020927599429347)
              ·
                refine ⟨2298854868031391399144021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1532569912020927599429347 2298854868031391399144021)
                ·
                  refine ⟨26939705484742867958719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2298854868031391399144021 26939705484742867958719)
                  ·
                    rfl

theorem cell23_472184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 8].length) (baseStart_472184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472184 prefixEnd_472184 := by exact prefixLift 472184
  have htrace : WordTrace (prefixWord ++ tailWord_472184) baseStart_472184 baseEnd_472184 := by
    simpa [prefixWord, tailWord_472184, baseEnd_472184] using wordTrace_append hprefix tailTrace_472184
  have hstable : (prefixWord ++ tailWord_472184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472184).length < 2 ^ (prefixWord ++ tailWord_472184).sum := by decide
  have hdescent : baseEnd_472184 < baseStart_472184 := by decide
  rcases family_descends (prefixWord ++ tailWord_472184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472190 : List Nat := [4, 2, 4, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_472190 : Nat := 118140960795 + 472190 * 2 ^ 59
def prefixEnd_472190 : Nat := 4983230072969 + 3 ^ 40 * 472190 * 2
def baseEnd_472190 : Nat := 242460430246612788153445

theorem tailTrace_472190 : CollatzResearch.WordTrace tailWord_472190 prefixEnd_472190 242460430246612788153445 := by
  unfold tailWord_472190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2152773019917968559592753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11481456106229165651161349 2152773019917968559592753)
  ·
    refine ⟨1614579764938476419694565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2152773019917968559592753 1614579764938476419694565)
    ·
      refine ⟨302733705925964328692731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1614579764938476419694565 302733705925964328692731)
      ·
        refine ⟨454100558888946493039097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302733705925964328692731 454100558888946493039097)
        ·
          refine ⟨340575419166709869779323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454100558888946493039097 340575419166709869779323)
          ·
            refine ⟨510863128750064804668985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340575419166709869779323 510863128750064804668985)
            ·
              refine ⟨383147346562548603501739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510863128750064804668985 383147346562548603501739)
              ·
                refine ⟨574721019843822905252609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383147346562548603501739 574721019843822905252609)
                ·
                  refine ⟨431040764882867178939457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574721019843822905252609 431040764882867178939457)
                  ·
                    refine ⟨323280573662150384204593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 431040764882867178939457 323280573662150384204593)
                    ·
                      refine ⟨242460430246612788153445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 323280573662150384204593 242460430246612788153445)
                      ·
                        rfl

theorem cell23_472190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_472190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472190 prefixEnd_472190 := by exact prefixLift 472190
  have htrace : WordTrace (prefixWord ++ tailWord_472190) baseStart_472190 baseEnd_472190 := by
    simpa [prefixWord, tailWord_472190, baseEnd_472190] using wordTrace_append hprefix tailTrace_472190
  have hstable : (prefixWord ++ tailWord_472190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472190).length < 2 ^ (prefixWord ++ tailWord_472190).sum := by decide
  have hdescent : baseEnd_472190 < baseStart_472190 := by decide
  rcases family_descends (prefixWord ++ tailWord_472190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472201 : List Nat := [1, 2, 1, 1, 4, 4, 1, 3, 6]
def baseStart_472201 : Nat := 118140960795 + 472201 * 2 ^ 59
def prefixEnd_472201 : Nat := 4983230072969 + 3 ^ 40 * 472201 * 2
def baseEnd_472201 : Nat := 26940675392645805012877

theorem tailTrace_472201 : CollatzResearch.WordTrace tailWord_472201 prefixEnd_472201 26940675392645805012877 := by
  unfold tailWord_472201
  simp only [CollatzResearch.WordTrace]
  refine ⟨17222585362303897355392457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11481723574869264903594971 17222585362303897355392457)
  ·
    refine ⟨12916939021727923016544343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17222585362303897355392457 12916939021727923016544343)
    ·
      refine ⟨19375408532591884524816515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12916939021727923016544343 19375408532591884524816515)
      ·
        refine ⟨29063112798887826787224773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19375408532591884524816515 29063112798887826787224773)
        ·
          refine ⟨5449333649791467522604645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29063112798887826787224773 5449333649791467522604645)
          ·
            refine ⟨1021750059335900160488371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5449333649791467522604645 1021750059335900160488371)
            ·
              refine ⟨1532625089003850240732557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021750059335900160488371 1532625089003850240732557)
              ·
                refine ⟨574734408376443840274709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1532625089003850240732557 574734408376443840274709)
                ·
                  refine ⟨26940675392645805012877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 574734408376443840274709 26940675392645805012877)
                  ·
                    rfl

theorem cell23_472201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 6].length) (baseStart_472201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472201 prefixEnd_472201 := by exact prefixLift 472201
  have htrace : WordTrace (prefixWord ++ tailWord_472201) baseStart_472201 baseEnd_472201 := by
    simpa [prefixWord, tailWord_472201, baseEnd_472201] using wordTrace_append hprefix tailTrace_472201
  have hstable : (prefixWord ++ tailWord_472201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472201).length < 2 ^ (prefixWord ++ tailWord_472201).sum := by decide
  have hdescent : baseEnd_472201 < baseStart_472201 := by decide
  rcases family_descends (prefixWord ++ tailWord_472201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472204 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 1, 2, 6]
def baseStart_472204 : Nat := 118140960795 + 472204 * 2 ^ 59
def prefixEnd_472204 : Nat := 4983230072969 + 3 ^ 40 * 472204 * 2
def baseEnd_472204 : Nat := 242467618975775733378379

theorem tailTrace_472204 : CollatzResearch.WordTrace tailWord_472204 prefixEnd_472204 242467618975775733378379 := by
  unfold tailWord_472204
  simp only [CollatzResearch.WordTrace]
  refine ⟨8611347390646514433875833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11481796520862019245167777 8611347390646514433875833)
  ·
    refine ⟨6458510542984885825406875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8611347390646514433875833 6458510542984885825406875)
    ·
      refine ⟨9687765814477328738110313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6458510542984885825406875 9687765814477328738110313)
      ·
        refine ⟨7265824360857996553582735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9687765814477328738110313 7265824360857996553582735)
        ·
          refine ⟨10898736541286994830374103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7265824360857996553582735 10898736541286994830374103)
          ·
            refine ⟨16348104811930492245561155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10898736541286994830374103 16348104811930492245561155)
            ·
              refine ⟨24522157217895738368341733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16348104811930492245561155 24522157217895738368341733)
              ·
                refine ⟨4597904478355450944064075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24522157217895738368341733 4597904478355450944064075)
                ·
                  refine ⟨6896856717533176416096113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4597904478355450944064075 6896856717533176416096113)
                  ·
                    refine ⟨5172642538149882312072085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6896856717533176416096113 5172642538149882312072085)
                    ·
                      refine ⟨242467618975775733378379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5172642538149882312072085 242467618975775733378379)
                      ·
                        rfl

theorem cell23_472204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_472204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472204 prefixEnd_472204 := by exact prefixLift 472204
  have htrace : WordTrace (prefixWord ++ tailWord_472204) baseStart_472204 baseEnd_472204 := by
    simpa [prefixWord, tailWord_472204, baseEnd_472204] using wordTrace_append hprefix tailTrace_472204
  have hstable : (prefixWord ++ tailWord_472204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472204).length < 2 ^ (prefixWord ++ tailWord_472204).sum := by decide
  have hdescent : baseEnd_472204 < baseStart_472204 := by decide
  rcases family_descends (prefixWord ++ tailWord_472204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472261 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 6, 4]
def baseStart_472261 : Nat := 118140960795 + 472261 * 2 ^ 59
def prefixEnd_472261 : Nat := 4983230072969 + 3 ^ 40 * 472261 * 2
def baseEnd_472261 : Nat := 80832295791027336788539

theorem tailTrace_472261 : CollatzResearch.WordTrace tailWord_472261 prefixEnd_472261 80832295791027336788539 := by
  unfold tailWord_472261
  simp only [CollatzResearch.WordTrace]
  refine ⟨17224773742086527602576637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11483182494724351735051091 17224773742086527602576637)
  ·
    refine ⟨6459290153282447850966239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17224773742086527602576637 6459290153282447850966239)
    ·
      refine ⟨9688935229923671776449359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6459290153282447850966239 9688935229923671776449359)
      ·
        refine ⟨14533402844885507664674039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9688935229923671776449359 14533402844885507664674039)
        ·
          refine ⟨21800104267328261497011059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14533402844885507664674039 21800104267328261497011059)
          ·
            refine ⟨32700156400992392245516589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21800104267328261497011059 32700156400992392245516589)
            ·
              refine ⟨12262558650372147092068721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32700156400992392245516589 12262558650372147092068721)
              ·
                refine ⟨9196918987779110319051541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12262558650372147092068721 9196918987779110319051541)
                ·
                  refine ⟨431105577552145796205541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9196918987779110319051541 431105577552145796205541)
                  ·
                    refine ⟨80832295791027336788539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 431105577552145796205541 80832295791027336788539)
                    ·
                      rfl

theorem cell23_472261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_472261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472261 prefixEnd_472261 := by exact prefixLift 472261
  have htrace : WordTrace (prefixWord ++ tailWord_472261) baseStart_472261 baseEnd_472261 := by
    simpa [prefixWord, tailWord_472261, baseEnd_472261] using wordTrace_append hprefix tailTrace_472261
  have hstable : (prefixWord ++ tailWord_472261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472261).length < 2 ^ (prefixWord ++ tailWord_472261).sum := by decide
  have hdescent : baseEnd_472261 < baseStart_472261 := by decide
  rcases family_descends (prefixWord ++ tailWord_472261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472295 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 4, 4]
def baseStart_472295 : Nat := 118140960795 + 472295 * 2 ^ 59
def prefixEnd_472295 : Nat := 4983230072969 + 3 ^ 40 * 472295 * 2
def baseEnd_472295 : Nat := 80838115238444959113487

theorem tailTrace_472295 : CollatzResearch.WordTrace tailWord_472295 prefixEnd_472295 80838115238444959113487 := by
  unfold tailWord_472295
  simp only [CollatzResearch.WordTrace]
  refine ⟨17226013823963351409314339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11484009215975567606209559 17226013823963351409314339)
  ·
    refine ⟨25839020735945027113971509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17226013823963351409314339 25839020735945027113971509)
    ·
      refine ⟨2422408193994846291934829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25839020735945027113971509 2422408193994846291934829)
      ·
        refine ⟨908403072748067359475561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2422408193994846291934829 908403072748067359475561)
        ·
          refine ⟨681302304561050519606671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 908403072748067359475561 681302304561050519606671)
          ·
            refine ⟨1021953456841575779410007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681302304561050519606671 1021953456841575779410007)
            ·
              refine ⟨1532930185262363669115011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021953456841575779410007 1532930185262363669115011)
              ·
                refine ⟨2299395277893545503672517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1532930185262363669115011 2299395277893545503672517)
                ·
                  refine ⟨431136614605039781938597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2299395277893545503672517 431136614605039781938597)
                  ·
                    refine ⟨80838115238444959113487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 431136614605039781938597 80838115238444959113487)
                    ·
                      rfl

theorem cell23_472295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_472295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472295 prefixEnd_472295 := by exact prefixLift 472295
  have htrace : WordTrace (prefixWord ++ tailWord_472295) baseStart_472295 baseEnd_472295 := by
    simpa [prefixWord, tailWord_472295, baseEnd_472295] using wordTrace_append hprefix tailTrace_472295
  have hstable : (prefixWord ++ tailWord_472295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472295).length < 2 ^ (prefixWord ++ tailWord_472295).sum := by decide
  have hdescent : baseEnd_472295 < baseStart_472295 := by decide
  rcases family_descends (prefixWord ++ tailWord_472295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472331 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 5]
def baseStart_472331 : Nat := 118140960795 + 472331 * 2 ^ 59
def prefixEnd_472331 : Nat := 4983230072969 + 3 ^ 40 * 472331 * 2
def baseEnd_472331 : Nat := 242532831018896736490295

theorem tailTrace_472331 : CollatzResearch.WordTrace tailWord_472331 prefixEnd_472331 242532831018896736490295 := by
  unfold tailWord_472331
  simp only [CollatzResearch.WordTrace]
  refine ⟨17227326851832929557624847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11484884567888619705083231 17227326851832929557624847)
  ·
    refine ⟨25840990277749394336437271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17227326851832929557624847 25840990277749394336437271)
    ·
      refine ⟨38761485416624091504655907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25840990277749394336437271 38761485416624091504655907)
      ·
        refine ⟨58142228124936137256983861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38761485416624091504655907 58142228124936137256983861)
        ·
          refine ⟨5450833886712762867842237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58142228124936137256983861 5450833886712762867842237)
          ·
            refine ⟨2044062707517286075440839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5450833886712762867842237 2044062707517286075440839)
            ·
              refine ⟨3066094061275929113161259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2044062707517286075440839 3066094061275929113161259)
              ·
                refine ⟨4599141091913893669741889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3066094061275929113161259 4599141091913893669741889)
                ·
                  refine ⟨3449355818935420252306417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4599141091913893669741889 3449355818935420252306417)
                  ·
                    refine ⟨2587016864201565189229813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3449355818935420252306417 2587016864201565189229813)
                    ·
                      refine ⟨242532831018896736490295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2587016864201565189229813 242532831018896736490295)
                      ·
                        rfl

theorem cell23_472331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 5].length) (baseStart_472331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472331 prefixEnd_472331 := by exact prefixLift 472331
  have htrace : WordTrace (prefixWord ++ tailWord_472331) baseStart_472331 baseEnd_472331 := by
    simpa [prefixWord, tailWord_472331, baseEnd_472331] using wordTrace_append hprefix tailTrace_472331
  have hstable : (prefixWord ++ tailWord_472331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472331).length < 2 ^ (prefixWord ++ tailWord_472331).sum := by decide
  have hdescent : baseEnd_472331 < baseStart_472331 := by decide
  rcases family_descends (prefixWord ++ tailWord_472331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472341 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_472341 : Nat := 118140960795 + 472341 * 2 ^ 59
def prefixEnd_472341 : Nat := 4983230072969 + 3 ^ 40 * 472341 * 2
def baseEnd_472341 : Nat := 242537965825441697365249

theorem tailTrace_472341 : CollatzResearch.WordTrace tailWord_472341 prefixEnd_472341 242537965825441697365249 := by
  unfold tailWord_472341
  simp only [CollatzResearch.WordTrace]
  refine ⟨17227691581796701265488877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11485127721197800843659251 17227691581796701265488877)
  ·
    refine ⟨6460384343173762974558329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17227691581796701265488877 6460384343173762974558329)
    ·
      refine ⟨4845288257380322230918747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6460384343173762974558329 4845288257380322230918747)
      ·
        refine ⟨7267932386070483346378121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4845288257380322230918747 7267932386070483346378121)
        ·
          refine ⟨5450949289552862509783591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7267932386070483346378121 5450949289552862509783591)
          ·
            refine ⟨8176423934329293764675387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5450949289552862509783591 8176423934329293764675387)
            ·
              refine ⟨12264635901493940647013081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8176423934329293764675387 12264635901493940647013081)
              ·
                refine ⟨9198476926120455485259811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12264635901493940647013081 9198476926120455485259811)
                ·
                  refine ⟨13797715389180683227889717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9198476926120455485259811 13797715389180683227889717)
                  ·
                    refine ⟨1293535817735689052614661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13797715389180683227889717 1293535817735689052614661)
                    ·
                      refine ⟨242537965825441697365249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1293535817735689052614661 242537965825441697365249)
                      ·
                        rfl

theorem cell23_472341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_472341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472341 prefixEnd_472341 := by exact prefixLift 472341
  have htrace : WordTrace (prefixWord ++ tailWord_472341) baseStart_472341 baseEnd_472341 := by
    simpa [prefixWord, tailWord_472341, baseEnd_472341] using wordTrace_append hprefix tailTrace_472341
  have hstable : (prefixWord ++ tailWord_472341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472341).length < 2 ^ (prefixWord ++ tailWord_472341).sum := by decide
  have hdescent : baseEnd_472341 < baseStart_472341 := by decide
  rcases family_descends (prefixWord ++ tailWord_472341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472369 : List Nat := [1, 2, 2, 3, 3, 3, 2, 1, 2, 1, 3]
def baseStart_472369 : Nat := 118140960795 + 472369 * 2 ^ 59
def prefixEnd_472369 : Nat := 4983230072969 + 3 ^ 40 * 472369 * 2
def baseEnd_472369 : Nat := 242552343283767587815121

theorem tailTrace_472369 : CollatzResearch.WordTrace tailWord_472369 prefixEnd_472369 242552343283767587815121 := by
  unfold tailWord_472369
  simp only [CollatzResearch.WordTrace]
  refine ⟨17228712825695262047508161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11485808550463508031672107 17228712825695262047508161)
  ·
    refine ⟨12921534619271446535631121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17228712825695262047508161 12921534619271446535631121)
    ·
      refine ⟨9691150964453584901723341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12921534619271446535631121 9691150964453584901723341)
      ·
        refine ⟨3634181611670094338146253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9691150964453584901723341 3634181611670094338146253)
        ·
          refine ⟨1362818104376285376804845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3634181611670094338146253 1362818104376285376804845)
          ·
            refine ⟨511056789141107016301817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1362818104376285376804845 511056789141107016301817)
            ·
              refine ⟨383292591855830262226363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511056789141107016301817 383292591855830262226363)
              ·
                refine ⟨574938887783745393339545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383292591855830262226363 574938887783745393339545)
                ·
                  refine ⟨431204165837809045004659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574938887783745393339545 431204165837809045004659)
                  ·
                    refine ⟨646806248756713567506989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 431204165837809045004659 646806248756713567506989)
                    ·
                      refine ⟨242552343283767587815121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 646806248756713567506989 242552343283767587815121)
                      ·
                        rfl

theorem cell23_472369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_472369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472369 prefixEnd_472369 := by exact prefixLift 472369
  have htrace : WordTrace (prefixWord ++ tailWord_472369) baseStart_472369 baseEnd_472369 := by
    simpa [prefixWord, tailWord_472369, baseEnd_472369] using wordTrace_append hprefix tailTrace_472369
  have hstable : (prefixWord ++ tailWord_472369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472369).length < 2 ^ (prefixWord ++ tailWord_472369).sum := by decide
  have hdescent : baseEnd_472369 < baseStart_472369 := by decide
  rcases family_descends (prefixWord ++ tailWord_472369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472408 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 2, 3, 3]
def baseStart_472408 : Nat := 118140960795 + 472408 * 2 ^ 59
def prefixEnd_472408 : Nat := 4983230072969 + 3 ^ 40 * 472408 * 2
def baseEnd_472408 : Nat := 242572369029292935227441

theorem tailTrace_472408 : CollatzResearch.WordTrace tailWord_472408 prefixEnd_472408 242572369029292935227441 := by
  unfold tailWord_472408
  simp only [CollatzResearch.WordTrace]
  refine ⟨8615067636276985854088939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11486756848369314472118585 8615067636276985854088939)
  ·
    refine ⟨12922601454415478781133409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8615067636276985854088939 12922601454415478781133409)
    ·
      refine ⟨9691951090811609085850057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12922601454415478781133409 9691951090811609085850057)
      ·
        refine ⟨7268963318108706814387543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9691951090811609085850057 7268963318108706814387543)
        ·
          refine ⟨10903444977163060221581315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7268963318108706814387543 10903444977163060221581315)
          ·
            refine ⟨16355167465744590332371973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10903444977163060221581315 16355167465744590332371973)
            ·
              refine ⟨3066593899827110687319745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16355167465744590332371973 3066593899827110687319745)
              ·
                refine ⟨2299945424870333015489809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3066593899827110687319745 2299945424870333015489809)
                ·
                  refine ⟨1724959068652749761617357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2299945424870333015489809 1724959068652749761617357)
                  ·
                    refine ⟨646859650744781160606509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1724959068652749761617357 646859650744781160606509)
                    ·
                      refine ⟨242572369029292935227441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 646859650744781160606509 242572369029292935227441)
                      ·
                        rfl

theorem cell23_472408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_472408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472408 prefixEnd_472408 := by exact prefixLift 472408
  have htrace : WordTrace (prefixWord ++ tailWord_472408) baseStart_472408 baseEnd_472408 := by
    simpa [prefixWord, tailWord_472408, baseEnd_472408] using wordTrace_append hprefix tailTrace_472408
  have hstable : (prefixWord ++ tailWord_472408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472408).length < 2 ^ (prefixWord ++ tailWord_472408).sum := by decide
  have hdescent : baseEnd_472408 < baseStart_472408 := by decide
  rcases family_descends (prefixWord ++ tailWord_472408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472482 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 2, 4, 2]
def baseStart_472482 : Nat := 118140960795 + 472482 * 2 ^ 59
def prefixEnd_472482 : Nat := 4983230072969 + 3 ^ 40 * 472482 * 2
def baseEnd_472482 : Nat := 242610366597725645702101

theorem tailTrace_472482 : CollatzResearch.WordTrace tailWord_472482 prefixEnd_472482 242610366597725645702101 := by
  unfold tailWord_472482
  simp only [CollatzResearch.WordTrace]
  refine ⟨4308208568571470586592925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11488556182857254897581133 4308208568571470586592925)
  ·
    refine ⟨1615578213214301469972347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4308208568571470586592925 1615578213214301469972347)
    ·
      refine ⟨2423367319821452204958521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1615578213214301469972347 2423367319821452204958521)
      ·
        refine ⟨1817525489866089153718891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2423367319821452204958521 1817525489866089153718891)
        ·
          refine ⟨2726288234799133730578337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1817525489866089153718891 2726288234799133730578337)
          ·
            refine ⟨2044716176099350297933753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2726288234799133730578337 2044716176099350297933753)
            ·
              refine ⟨1533537132074512723450315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2044716176099350297933753 1533537132074512723450315)
              ·
                refine ⟨2300305698111769085175473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1533537132074512723450315 2300305698111769085175473)
                ·
                  refine ⟨1725229273583826813881605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2300305698111769085175473 1725229273583826813881605)
                  ·
                    refine ⟨323480488796967527602801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1725229273583826813881605 323480488796967527602801)
                    ·
                      refine ⟨242610366597725645702101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 323480488796967527602801 242610366597725645702101)
                      ·
                        rfl

theorem cell23_472482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_472482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472482 prefixEnd_472482 := by exact prefixLift 472482
  have htrace : WordTrace (prefixWord ++ tailWord_472482) baseStart_472482 baseEnd_472482 := by
    simpa [prefixWord, tailWord_472482, baseEnd_472482] using wordTrace_append hprefix tailTrace_472482
  have hstable : (prefixWord ++ tailWord_472482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472482).length < 2 ^ (prefixWord ++ tailWord_472482).sum := by decide
  have hdescent : baseEnd_472482 < baseStart_472482 := by decide
  rcases family_descends (prefixWord ++ tailWord_472482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472515 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 5, 1, 3]
def baseStart_472515 : Nat := 118140960795 + 472515 * 2 ^ 59
def prefixEnd_472515 : Nat := 4983230072969 + 3 ^ 40 * 472515 * 2
def baseEnd_472515 : Nat := 242627311459324016589449

theorem tailTrace_472515 : CollatzResearch.WordTrace tailWord_472515 prefixEnd_472515 242627311459324016589449 := by
  unfold tailWord_472515
  simp only [CollatzResearch.WordTrace]
  refine ⟨17234037883166328982322999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11489358588777552654881999 17234037883166328982322999)
  ·
    refine ⟨25851056824749493473484499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17234037883166328982322999 25851056824749493473484499)
    ·
      refine ⟨38776585237124240210226749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25851056824749493473484499 38776585237124240210226749)
      ·
        refine ⟨14541219463921590078835031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38776585237124240210226749 14541219463921590078835031)
        ·
          refine ⟨21811829195882385118252547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14541219463921590078835031 21811829195882385118252547)
          ·
            refine ⟨32717743793823577677378821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21811829195882385118252547 32717743793823577677378821)
            ·
              refine ⟨6134576961341920814508529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32717743793823577677378821 6134576961341920814508529)
              ·
                refine ⟨4600932721006440610881397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6134576961341920814508529 4600932721006440610881397)
                ·
                  refine ⟨431337442594353807270131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4600932721006440610881397 431337442594353807270131)
                  ·
                    refine ⟨647006163891530710905197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 431337442594353807270131 647006163891530710905197)
                    ·
                      refine ⟨242627311459324016589449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 647006163891530710905197 242627311459324016589449)
                      ·
                        rfl

theorem cell23_472515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 1, 3].length) (baseStart_472515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472515 prefixEnd_472515 := by exact prefixLift 472515
  have htrace : WordTrace (prefixWord ++ tailWord_472515) baseStart_472515 baseEnd_472515 := by
    simpa [prefixWord, tailWord_472515, baseEnd_472515] using wordTrace_append hprefix tailTrace_472515
  have hstable : (prefixWord ++ tailWord_472515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472515).length < 2 ^ (prefixWord ++ tailWord_472515).sum := by decide
  have hdescent : baseEnd_472515 < baseStart_472515 := by decide
  rcases family_descends (prefixWord ++ tailWord_472515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472548 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 5, 6]
def baseStart_472548 : Nat := 118140960795 + 472548 * 2 ^ 59
def prefixEnd_472548 : Nat := 4983230072969 + 3 ^ 40 * 472548 * 2
def baseEnd_472548 : Nat := 80881418773640795825599

theorem tailTrace_472548 : CollatzResearch.WordTrace tailWord_472548 prefixEnd_472548 80881418773640795825599 := by
  unfold tailWord_472548
  simp only [CollatzResearch.WordTrace]
  refine ⟨8617620746023387809137149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11490160994697850412182865 8617620746023387809137149)
  ·
    refine ⟨3231607779758770428426431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8617620746023387809137149 3231607779758770428426431)
    ·
      refine ⟨4847411669638155642639647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3231607779758770428426431 4847411669638155642639647)
      ·
        refine ⟨7271117504457233463959471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4847411669638155642639647 7271117504457233463959471)
        ·
          refine ⟨10906676256685850195939207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7271117504457233463959471 10906676256685850195939207)
          ·
            refine ⟨16360014385028775293908811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10906676256685850195939207 16360014385028775293908811)
            ·
              refine ⟨24540021577543162940863217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16360014385028775293908811 24540021577543162940863217)
              ·
                refine ⟨18405016183157372205647413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24540021577543162940863217 18405016183157372205647413)
                ·
                  refine ⟨1725470267171003644279445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18405016183157372205647413 1725470267171003644279445)
                  ·
                    refine ⟨80881418773640795825599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1725470267171003644279445 80881418773640795825599)
                    ·
                      rfl

theorem cell23_472548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_472548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472548 prefixEnd_472548 := by exact prefixLift 472548
  have htrace : WordTrace (prefixWord ++ tailWord_472548) baseStart_472548 baseEnd_472548 := by
    simpa [prefixWord, tailWord_472548, baseEnd_472548] using wordTrace_append hprefix tailTrace_472548
  have hstable : (prefixWord ++ tailWord_472548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472548).length < 2 ^ (prefixWord ++ tailWord_472548).sum := by decide
  have hdescent : baseEnd_472548 < baseStart_472548 := by decide
  rcases family_descends (prefixWord ++ tailWord_472548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472555 : List Nat := [1, 1, 1, 1, 2, 3, 2, 6, 1, 1, 4]
def baseStart_472555 : Nat := 118140960795 + 472555 * 2 ^ 59
def prefixEnd_472555 : Nat := 4983230072969 + 3 ^ 40 * 472555 * 2
def baseEnd_472555 : Nat := 242647850685503860089265

theorem tailTrace_472555 : CollatzResearch.WordTrace tailWord_472555 prefixEnd_472555 242647850685503860089265 := by
  unfold tailWord_472555
  simp only [CollatzResearch.WordTrace]
  refine ⟨17235496803021415813779119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11490331202014277209186079 17235496803021415813779119)
  ·
    refine ⟨25853245204532123720668679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17235496803021415813779119 25853245204532123720668679)
    ·
      refine ⟨38779867806798185581003019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25853245204532123720668679 38779867806798185581003019)
      ·
        refine ⟨58169801710197278371504529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38779867806798185581003019 58169801710197278371504529)
        ·
          refine ⟨43627351282647958778628397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58169801710197278371504529 43627351282647958778628397)
          ·
            refine ⟨16360256730992984541985649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43627351282647958778628397 16360256730992984541985649)
            ·
              refine ⟨12270192548244738406489237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16360256730992984541985649 12270192548244738406489237)
              ·
                refine ⟨575165275698972112804183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12270192548244738406489237 575165275698972112804183)
                ·
                  refine ⟨862747913548458169206275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575165275698972112804183 862747913548458169206275)
                  ·
                    refine ⟨1294121870322687253809413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 862747913548458169206275 1294121870322687253809413)
                    ·
                      refine ⟨242647850685503860089265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1294121870322687253809413 242647850685503860089265)
                      ·
                        rfl

theorem cell23_472555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 1, 4].length) (baseStart_472555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472555 prefixEnd_472555 := by exact prefixLift 472555
  have htrace : WordTrace (prefixWord ++ tailWord_472555) baseStart_472555 baseEnd_472555 := by
    simpa [prefixWord, tailWord_472555, baseEnd_472555] using wordTrace_append hprefix tailTrace_472555
  have hstable : (prefixWord ++ tailWord_472555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472555).length < 2 ^ (prefixWord ++ tailWord_472555).sum := by decide
  have hdescent : baseEnd_472555 < baseStart_472555 := by decide
  rcases family_descends (prefixWord ++ tailWord_472555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472583 : List Nat := [1, 1, 4, 3, 2, 3, 2, 2, 1, 1, 3]
def baseStart_472583 : Nat := 118140960795 + 472583 * 2 ^ 59
def prefixEnd_472583 : Nat := 4983230072969 + 3 ^ 40 * 472583 * 2
def baseEnd_472583 : Nat := 242662228143829750539137

theorem tailTrace_472583 : CollatzResearch.WordTrace tailWord_472583 prefixEnd_472583 242662228143829750539137 := by
  unfold tailWord_472583
  simp only [CollatzResearch.WordTrace]
  refine ⟨17236518046919976595798403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11491012031279984397198935 17236518046919976595798403)
  ·
    refine ⟨25854777070379964893697605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17236518046919976595798403 25854777070379964893697605)
    ·
      refine ⟨4847770700696243417568301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25854777070379964893697605 4847770700696243417568301)
      ·
        refine ⟨1817914012761091281588113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4847770700696243417568301 1817914012761091281588113)
        ·
          refine ⟨1363435509570818461191085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1817914012761091281588113 1363435509570818461191085)
          ·
            refine ⟨511288316089056922946657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1363435509570818461191085 511288316089056922946657)
            ·
              refine ⟨383466237066792692209993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511288316089056922946657 383466237066792692209993)
              ·
                refine ⟨287599677800094519157495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383466237066792692209993 287599677800094519157495)
                ·
                  refine ⟨431399516700141778736243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287599677800094519157495 431399516700141778736243)
                  ·
                    refine ⟨647099275050212668104365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 431399516700141778736243 647099275050212668104365)
                    ·
                      refine ⟨242662228143829750539137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 647099275050212668104365 242662228143829750539137)
                      ·
                        rfl

theorem cell23_472583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_472583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472583 prefixEnd_472583 := by exact prefixLift 472583
  have htrace : WordTrace (prefixWord ++ tailWord_472583) baseStart_472583 baseEnd_472583 := by
    simpa [prefixWord, tailWord_472583, baseEnd_472583] using wordTrace_append hprefix tailTrace_472583
  have hstable : (prefixWord ++ tailWord_472583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472583).length < 2 ^ (prefixWord ++ tailWord_472583).sum := by decide
  have hdescent : baseEnd_472583 < baseStart_472583 := by decide
  rcases family_descends (prefixWord ++ tailWord_472583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472595 : List Nat := [1, 1, 1, 2, 1, 8, 1, 8]
def baseStart_472595 : Nat := 118140960795 + 472595 * 2 ^ 59
def prefixEnd_472595 : Nat := 4983230072969 + 3 ^ 40 * 472595 * 2
def baseEnd_472595 : Nat := 8987718144877174207003

theorem tailTrace_472595 : CollatzResearch.WordTrace tailWord_472595 prefixEnd_472595 8987718144877174207003 := by
  unfold tailWord_472595
  simp only [CollatzResearch.WordTrace]
  refine ⟨17236955722876502645235239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11491303815251001763490159 17236955722876502645235239)
  ·
    refine ⟨25855433584314753967852859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17236955722876502645235239 25855433584314753967852859)
    ·
      refine ⟨38783150376472130951779289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25855433584314753967852859 38783150376472130951779289)
      ·
        refine ⟨29087362782354098213834467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38783150376472130951779289 29087362782354098213834467)
        ·
          refine ⟨43631044173531147320751701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29087362782354098213834467 43631044173531147320751701)
          ·
            refine ⟨511301298908568132665059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 43631044173531147320751701 511301298908568132665059)
            ·
              refine ⟨766951948362852198997589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511301298908568132665059 766951948362852198997589)
              ·
                refine ⟨8987718144877174207003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 766951948362852198997589 8987718144877174207003)
                ·
                  rfl

theorem cell23_472595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 8].length) (baseStart_472595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472595 prefixEnd_472595 := by exact prefixLift 472595
  have htrace : WordTrace (prefixWord ++ tailWord_472595) baseStart_472595 baseEnd_472595 := by
    simpa [prefixWord, tailWord_472595, baseEnd_472595] using wordTrace_append hprefix tailTrace_472595
  have hstable : (prefixWord ++ tailWord_472595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472595).length < 2 ^ (prefixWord ++ tailWord_472595).sum := by decide
  have hdescent : baseEnd_472595 < baseStart_472595 := by decide
  rcases family_descends (prefixWord ++ tailWord_472595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472639 : List Nat := [1, 1, 2, 2, 3, 3, 3, 2, 2, 1, 3]
def baseStart_472639 : Nat := 118140960795 + 472639 * 2 ^ 59
def prefixEnd_472639 : Nat := 4983230072969 + 3 ^ 40 * 472639 * 2
def baseEnd_472639 : Nat := 242690983060481531438879

theorem tailTrace_472639 : CollatzResearch.WordTrace tailWord_472639 prefixEnd_472639 242690983060481531438879 := by
  unfold tailWord_472639
  simp only [CollatzResearch.WordTrace]
  refine ⟨17238560534717098159836971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11492373689811398773224647 17238560534717098159836971)
  ·
    refine ⟨25857840802075647239755457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17238560534717098159836971 25857840802075647239755457)
    ·
      refine ⟨19393380601556735429816593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25857840802075647239755457 19393380601556735429816593)
      ·
        refine ⟨14545035451167551572362445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19393380601556735429816593 14545035451167551572362445)
        ·
          refine ⟨5454388294187831839635917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14545035451167551572362445 5454388294187831839635917)
          ·
            refine ⟨2045395610320436939863469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5454388294187831839635917 2045395610320436939863469)
            ·
              refine ⟨767023353870163852448801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2045395610320436939863469 767023353870163852448801)
              ·
                refine ⟨575267515402622889336601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767023353870163852448801 575267515402622889336601)
                ·
                  refine ⟨431450636551967167002451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575267515402622889336601 431450636551967167002451)
                  ·
                    refine ⟨647175954827950750503677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 431450636551967167002451 647175954827950750503677)
                    ·
                      refine ⟨242690983060481531438879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 647175954827950750503677 242690983060481531438879)
                      ·
                        rfl

theorem cell23_472639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 1, 3].length) (baseStart_472639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472639 prefixEnd_472639 := by exact prefixLift 472639
  have htrace : WordTrace (prefixWord ++ tailWord_472639) baseStart_472639 baseEnd_472639 := by
    simpa [prefixWord, tailWord_472639, baseEnd_472639] using wordTrace_append hprefix tailTrace_472639
  have hstable : (prefixWord ++ tailWord_472639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472639).length < 2 ^ (prefixWord ++ tailWord_472639).sum := by decide
  have hdescent : baseEnd_472639 < baseStart_472639 := by decide
  rcases family_descends (prefixWord ++ tailWord_472639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472665 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 2, 4, 3]
def baseStart_472665 : Nat := 118140960795 + 472665 * 2 ^ 59
def prefixEnd_472665 : Nat := 4983230072969 + 3 ^ 40 * 472665 * 2
def baseEnd_472665 : Nat := 242704333557498429713759

theorem tailTrace_472665 : CollatzResearch.WordTrace tailWord_472665 prefixEnd_472665 242704333557498429713759 := by
  unfold tailWord_472665
  simp only [CollatzResearch.WordTrace]
  refine ⟨17239508832622904600283449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11493005888415269733522299 17239508832622904600283449)
  ·
    refine ⟨12929631624467178450212587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17239508832622904600283449 12929631624467178450212587)
    ·
      refine ⟨19394447436700767675318881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12929631624467178450212587 19394447436700767675318881)
      ·
        refine ⟨14545835577525575756489161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19394447436700767675318881 14545835577525575756489161)
        ·
          refine ⟨10909376683144181817366871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14545835577525575756489161 10909376683144181817366871)
          ·
            refine ⟨16364065024716272726050307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10909376683144181817366871 16364065024716272726050307)
            ·
              refine ⟨24546097537074409089075461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16364065024716272726050307 24546097537074409089075461)
              ·
                refine ⟨4602393288201451704201649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24546097537074409089075461 4602393288201451704201649)
                ·
                  refine ⟨3451794966151088778151237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4602393288201451704201649 3451794966151088778151237)
                  ·
                    refine ⟨647211556153329145903357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3451794966151088778151237 647211556153329145903357)
                    ·
                      refine ⟨242704333557498429713759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 647211556153329145903357 242704333557498429713759)
                      ·
                        rfl

theorem cell23_472665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_472665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472665 prefixEnd_472665 := by exact prefixLift 472665
  have htrace : WordTrace (prefixWord ++ tailWord_472665) baseStart_472665 baseEnd_472665 := by
    simpa [prefixWord, tailWord_472665, baseEnd_472665] using wordTrace_append hprefix tailTrace_472665
  have hstable : (prefixWord ++ tailWord_472665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472665).length < 2 ^ (prefixWord ++ tailWord_472665).sum := by decide
  have hdescent : baseEnd_472665 < baseStart_472665 := by decide
  rcases family_descends (prefixWord ++ tailWord_472665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472679 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 4, 2, 2]
def baseStart_472679 : Nat := 118140960795 + 472679 * 2 ^ 59
def prefixEnd_472679 : Nat := 4983230072969 + 3 ^ 40 * 472679 * 2
def baseEnd_472679 : Nat := 242711522286661374938695

theorem tailTrace_472679 : CollatzResearch.WordTrace tailWord_472679 prefixEnd_472679 242711522286661374938695 := by
  unfold tailWord_472679
  simp only [CollatzResearch.WordTrace]
  refine ⟨17240019454572184991293091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11493346303048123327528727 17240019454572184991293091)
  ·
    refine ⟨25860029181858277486939637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17240019454572184991293091 25860029181858277486939637)
    ·
      refine ⟨2424377735799213514400591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25860029181858277486939637 2424377735799213514400591)
      ·
        refine ⟨3636566603698820271600887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2424377735799213514400591 3636566603698820271600887)
        ·
          refine ⟨5454849905548230407401331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3636566603698820271600887 5454849905548230407401331)
          ·
            refine ⟨8182274858322345611101997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5454849905548230407401331 8182274858322345611101997)
            ·
              refine ⟨3068353071870879604163249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8182274858322345611101997 3068353071870879604163249)
              ·
                refine ⟨2301264803903159703122437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3068353071870879604163249 2301264803903159703122437)
                ·
                  refine ⟨431487150731842444335457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2301264803903159703122437 431487150731842444335457)
                  ·
                    refine ⟨323615363048881833251593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 431487150731842444335457 323615363048881833251593)
                    ·
                      refine ⟨242711522286661374938695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 323615363048881833251593 242711522286661374938695)
                      ·
                        rfl

theorem cell23_472679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_472679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472679 prefixEnd_472679 := by exact prefixLift 472679
  have htrace : WordTrace (prefixWord ++ tailWord_472679) baseStart_472679 baseEnd_472679 := by
    simpa [prefixWord, tailWord_472679, baseEnd_472679] using wordTrace_append hprefix tailTrace_472679
  have hstable : (prefixWord ++ tailWord_472679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472679).length < 2 ^ (prefixWord ++ tailWord_472679).sum := by decide
  have hdescent : baseEnd_472679 < baseStart_472679 := by decide
  rcases family_descends (prefixWord ++ tailWord_472679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472682 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_472682 : Nat := 118140960795 + 472682 * 2 ^ 59
def prefixEnd_472682 : Nat := 4983230072969 + 3 ^ 40 * 472682 * 2
def baseEnd_472682 : Nat := 242713062728624863201181

theorem tailTrace_472682 : CollatzResearch.WordTrace tailWord_472682 prefixEnd_472682 242713062728624863201181 := by
  unfold tailWord_472682
  simp only [CollatzResearch.WordTrace]
  refine ⟨4310032218390329125913075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11493419249040877669101533 4310032218390329125913075)
  ·
    refine ⟨6465048327585493688869613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4310032218390329125913075 6465048327585493688869613)
    ·
      refine ⟨2424393122844560133326105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6465048327585493688869613 2424393122844560133326105)
      ·
        refine ⟨1818294842133420099994579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2424393122844560133326105 1818294842133420099994579)
        ·
          refine ⟨2727442263200130149991869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818294842133420099994579 2727442263200130149991869)
          ·
            refine ⟨1022790848700048806246951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2727442263200130149991869 1022790848700048806246951)
            ·
              refine ⟨1534186273050073209370427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1022790848700048806246951 1534186273050073209370427)
              ·
                refine ⟨2301279409575109814055641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534186273050073209370427 2301279409575109814055641)
                ·
                  refine ⟨1725959557181332360541731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2301279409575109814055641 1725959557181332360541731)
                  ·
                    refine ⟨2588939335771998540812597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1725959557181332360541731 2588939335771998540812597)
                    ·
                      refine ⟨242713062728624863201181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2588939335771998540812597 242713062728624863201181)
                      ·
                        rfl

theorem cell23_472682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_472682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472682 prefixEnd_472682 := by exact prefixLift 472682
  have htrace : WordTrace (prefixWord ++ tailWord_472682) baseStart_472682 baseEnd_472682 := by
    simpa [prefixWord, tailWord_472682, baseEnd_472682] using wordTrace_append hprefix tailTrace_472682
  have hstable : (prefixWord ++ tailWord_472682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472682).length < 2 ^ (prefixWord ++ tailWord_472682).sum := by decide
  have hdescent : baseEnd_472682 < baseStart_472682 := by decide
  rcases family_descends (prefixWord ++ tailWord_472682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472715 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 4, 5]
def baseStart_472715 : Nat := 118140960795 + 472715 * 2 ^ 59
def prefixEnd_472715 : Nat := 4983230072969 + 3 ^ 40 * 472715 * 2
def baseEnd_472715 : Nat := 80910002530074411362843

theorem tailTrace_472715 : CollatzResearch.WordTrace tailWord_472715 prefixEnd_472715 80910002530074411362843 := by
  unfold tailWord_472715
  simp only [CollatzResearch.WordTrace]
  refine ⟨17241332482441763139603599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11494221654961175426402399 17241332482441763139603599)
  ·
    refine ⟨25861998723662644709405399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17241332482441763139603599 25861998723662644709405399)
    ·
      refine ⟨38792998085493967064108099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25861998723662644709405399 38792998085493967064108099)
      ·
        refine ⟨58189497128240950596162149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38792998085493967064108099 58189497128240950596162149)
        ·
          refine ⟨10910530711545178236780403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58189497128240950596162149 10910530711545178236780403)
          ·
            refine ⟨16365796067317767355170605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10910530711545178236780403 16365796067317767355170605)
            ·
              refine ⟨6137173525244162758188977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16365796067317767355170605 6137173525244162758188977)
              ·
                refine ⟨4602880143933122068641733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6137173525244162758188977 4602880143933122068641733)
                ·
                  refine ⟨863040026987460387870325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4602880143933122068641733 863040026987460387870325)
                  ·
                    refine ⟨80910002530074411362843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 863040026987460387870325 80910002530074411362843)
                    ·
                      rfl

theorem cell23_472715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 5].length) (baseStart_472715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472715 prefixEnd_472715 := by exact prefixLift 472715
  have htrace : WordTrace (prefixWord ++ tailWord_472715) baseStart_472715 baseEnd_472715 := by
    simpa [prefixWord, tailWord_472715, baseEnd_472715] using wordTrace_append hprefix tailTrace_472715
  have hstable : (prefixWord ++ tailWord_472715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472715).length < 2 ^ (prefixWord ++ tailWord_472715).sum := by decide
  have hdescent : baseEnd_472715 < baseStart_472715 := by decide
  rcases family_descends (prefixWord ++ tailWord_472715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472752 : List Nat := [2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 4]
def baseStart_472752 : Nat := 118140960795 + 472752 * 2 ^ 59
def prefixEnd_472752 : Nat := 4983230072969 + 3 ^ 40 * 472752 * 2
def baseEnd_472752 : Nat := 242749006374439589325859

theorem tailTrace_472752 : CollatzResearch.WordTrace tailWord_472752 prefixEnd_472752 242749006374439589325859 := by
  unfold tailWord_472752
  simp only [CollatzResearch.WordTrace]
  refine ⟨8621340991653859229350255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11495121322205145639133673 8621340991653859229350255)
  ·
    refine ⟨12932011487480788844025383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8621340991653859229350255 12932011487480788844025383)
    ·
      refine ⟨19398017231221183266038075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12932011487480788844025383 19398017231221183266038075)
      ·
        refine ⟨29097025846831774899057113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19398017231221183266038075 29097025846831774899057113)
        ·
          refine ⟨21822769385123831174292835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29097025846831774899057113 21822769385123831174292835)
          ·
            refine ⟨32734154077685746761439253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21822769385123831174292835 32734154077685746761439253)
            ·
              refine ⟨1534413472391519379442465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32734154077685746761439253 1534413472391519379442465)
              ·
                refine ⟨1150810104293639534581849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1534413472391519379442465 1150810104293639534581849)
                ·
                  refine ⟨863107578220229650936387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1150810104293639534581849 863107578220229650936387)
                  ·
                    refine ⟨1294661367330344476404581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 863107578220229650936387 1294661367330344476404581)
                    ·
                      refine ⟨242749006374439589325859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1294661367330344476404581 242749006374439589325859)
                      ·
                        rfl

theorem cell23_472752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 4].length) (baseStart_472752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472752 prefixEnd_472752 := by exact prefixLift 472752
  have htrace : WordTrace (prefixWord ++ tailWord_472752) baseStart_472752 baseEnd_472752 := by
    simpa [prefixWord, tailWord_472752, baseEnd_472752] using wordTrace_append hprefix tailTrace_472752
  have hstable : (prefixWord ++ tailWord_472752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472752).length < 2 ^ (prefixWord ++ tailWord_472752).sum := by decide
  have hdescent : baseEnd_472752 < baseStart_472752 := by decide
  rcases family_descends (prefixWord ++ tailWord_472752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472755 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 5]
def baseStart_472755 : Nat := 118140960795 + 472755 * 2 ^ 59
def prefixEnd_472755 : Nat := 4983230072969 + 3 ^ 40 * 472755 * 2
def baseEnd_472755 : Nat := 242750546816403077588345

theorem tailTrace_472755 : CollatzResearch.WordTrace tailWord_472755 prefixEnd_472755 242750546816403077588345 := by
  unfold tailWord_472755
  simp only [CollatzResearch.WordTrace]
  refine ⟨17242791402296849971059719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11495194268197899980706479 17242791402296849971059719)
  ·
    refine ⟨25864187103445274956589579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17242791402296849971059719 25864187103445274956589579)
    ·
      refine ⟨38796280655167912434884369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25864187103445274956589579 38796280655167912434884369)
      ·
        refine ⟨29097210491375934326163277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38796280655167912434884369 29097210491375934326163277)
        ·
          refine ⟨10911453934265975372311229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29097210491375934326163277 10911453934265975372311229)
          ·
            refine ⟨4091795225349740764616711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10911453934265975372311229 4091795225349740764616711)
            ·
              refine ⟨6137692838024611146925067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4091795225349740764616711 6137692838024611146925067)
              ·
                refine ⟨9206539257036916720387601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6137692838024611146925067 9206539257036916720387601)
                ·
                  refine ⟨6904904442777687540290701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9206539257036916720387601 6904904442777687540290701)
                  ·
                    refine ⟨2589339166041632827609013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6904904442777687540290701 2589339166041632827609013)
                    ·
                      refine ⟨242750546816403077588345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2589339166041632827609013 242750546816403077588345)
                      ·
                        rfl

theorem cell23_472755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_472755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472755 prefixEnd_472755 := by exact prefixLift 472755
  have htrace : WordTrace (prefixWord ++ tailWord_472755) baseStart_472755 baseEnd_472755 := by
    simpa [prefixWord, tailWord_472755, baseEnd_472755] using wordTrace_append hprefix tailTrace_472755
  have hstable : (prefixWord ++ tailWord_472755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472755).length < 2 ^ (prefixWord ++ tailWord_472755).sum := by decide
  have hdescent : baseEnd_472755 < baseStart_472755 := by decide
  rcases family_descends (prefixWord ++ tailWord_472755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472786 : List Nat := [3, 2, 2, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_472786 : Nat := 118140960795 + 472786 * 2 ^ 59
def prefixEnd_472786 : Nat := 4983230072969 + 3 ^ 40 * 472786 * 2
def baseEnd_472786 : Nat := 242766464716692456300703

theorem tailTrace_472786 : CollatzResearch.WordTrace tailWord_472786 prefixEnd_472786 242766464716692456300703 := by
  unfold tailWord_472786
  simp only [CollatzResearch.WordTrace]
  refine ⟨4310980516296135566359553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11495948043456361510292141 4310980516296135566359553)
  ·
    refine ⟨3233235387222101674769665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4310980516296135566359553 3233235387222101674769665)
    ·
      refine ⟨2424926540416576256077249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3233235387222101674769665 2424926540416576256077249)
      ·
        refine ⟨1818694905312432192057937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2424926540416576256077249 1818694905312432192057937)
        ·
          refine ⟨1364021178984324144043453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1818694905312432192057937 1364021178984324144043453)
          ·
            refine ⟨511507942119121554016295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1364021178984324144043453 511507942119121554016295)
            ·
              refine ⟨767261913178682331024443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511507942119121554016295 767261913178682331024443)
              ·
                refine ⟨1150892869768023496536665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767261913178682331024443 1150892869768023496536665)
                ·
                  refine ⟨863169652326017622402499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1150892869768023496536665 863169652326017622402499)
                  ·
                    refine ⟨1294754478489026433603749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 863169652326017622402499 1294754478489026433603749)
                    ·
                      refine ⟨242766464716692456300703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1294754478489026433603749 242766464716692456300703)
                      ·
                        rfl

theorem cell23_472786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_472786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472786 prefixEnd_472786 := by exact prefixLift 472786
  have htrace : WordTrace (prefixWord ++ tailWord_472786) baseStart_472786 baseEnd_472786 := by
    simpa [prefixWord, tailWord_472786, baseEnd_472786] using wordTrace_append hprefix tailTrace_472786
  have hstable : (prefixWord ++ tailWord_472786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472786).length < 2 ^ (prefixWord ++ tailWord_472786).sum := by decide
  have hdescent : baseEnd_472786 < baseStart_472786 := by decide
  rcases family_descends (prefixWord ++ tailWord_472786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472819 : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 3, 1, 3]
def baseStart_472819 : Nat := 118140960795 + 472819 * 2 ^ 59
def prefixEnd_472819 : Nat := 4983230072969 + 3 ^ 40 * 472819 * 2
def baseEnd_472819 : Nat := 242783409578290827188051

theorem tailTrace_472819 : CollatzResearch.WordTrace tailWord_472819 prefixEnd_472819 242783409578290827188051 := by
  unfold tailWord_472819
  simp only [CollatzResearch.WordTrace]
  refine ⟨17245125674064988901389511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11496750449376659267593007 17245125674064988901389511)
  ·
    refine ⟨25867688511097483352084267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17245125674064988901389511 25867688511097483352084267)
    ·
      refine ⟨38801532766646225028126401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25867688511097483352084267 38801532766646225028126401)
      ·
        refine ⟨29101149574984668771094801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38801532766646225028126401 29101149574984668771094801)
        ·
          refine ⟨21825862181238501578321101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29101149574984668771094801 21825862181238501578321101)
          ·
            refine ⟨8184698317964438091870413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21825862181238501578321101 8184698317964438091870413)
            ·
              refine ⟨3069261869236664284451405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8184698317964438091870413 3069261869236664284451405)
              ·
                refine ⟨1150973200963749106669277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3069261869236664284451405 1150973200963749106669277)
                ·
                  refine ⟨431614950361405915000979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1150973200963749106669277 431614950361405915000979)
                  ·
                    refine ⟨647422425542108872501469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 431614950361405915000979 647422425542108872501469)
                    ·
                      refine ⟨242783409578290827188051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 647422425542108872501469 242783409578290827188051)
                      ·
                        rfl

theorem cell23_472819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 1, 3].length) (baseStart_472819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472819 prefixEnd_472819 := by exact prefixLift 472819
  have htrace : WordTrace (prefixWord ++ tailWord_472819) baseStart_472819 baseEnd_472819 := by
    simpa [prefixWord, tailWord_472819, baseEnd_472819] using wordTrace_append hprefix tailTrace_472819
  have hstable : (prefixWord ++ tailWord_472819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472819).length < 2 ^ (prefixWord ++ tailWord_472819).sum := by decide
  have hdescent : baseEnd_472819 < baseStart_472819 := by decide
  rcases family_descends (prefixWord ++ tailWord_472819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472829 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 6, 3, 2]
def baseStart_472829 : Nat := 118140960795 + 472829 * 2 ^ 59
def prefixEnd_472829 : Nat := 4983230072969 + 3 ^ 40 * 472829 * 2
def baseEnd_472829 : Nat := 242788544384835788063005

theorem tailTrace_472829 : CollatzResearch.WordTrace tailWord_472829 prefixEnd_472829 242788544384835788063005 := by
  unfold tailWord_472829
  simp only [CollatzResearch.WordTrace]
  refine ⟨17245490404028760609253541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11496993602685840406169027 17245490404028760609253541)
  ·
    refine ⟨3233529450755392614235039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17245490404028760609253541 3233529450755392614235039)
    ·
      refine ⟨4850294176133088921352559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3233529450755392614235039 4850294176133088921352559)
      ·
        refine ⟨7275441264199633382028839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4850294176133088921352559 7275441264199633382028839)
        ·
          refine ⟨10913161896299450073043259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7275441264199633382028839 10913161896299450073043259)
          ·
            refine ⟨16369742844449175109564889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10913161896299450073043259 16369742844449175109564889)
            ·
              refine ⟨12277307133336881332173667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16369742844449175109564889 12277307133336881332173667)
              ·
                refine ⟨18415960700005321998260501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12277307133336881332173667 18415960700005321998260501)
                ·
                  refine ⟨863248157812749468668461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18415960700005321998260501 863248157812749468668461)
                  ·
                    refine ⟨323718059179781050750673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 863248157812749468668461 323718059179781050750673)
                    ·
                      refine ⟨242788544384835788063005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 323718059179781050750673 242788544384835788063005)
                      ·
                        rfl

theorem cell23_472829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_472829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472829 prefixEnd_472829 := by exact prefixLift 472829
  have htrace : WordTrace (prefixWord ++ tailWord_472829) baseStart_472829 baseEnd_472829 := by
    simpa [prefixWord, tailWord_472829, baseEnd_472829] using wordTrace_append hprefix tailTrace_472829
  have hstable : (prefixWord ++ tailWord_472829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472829).length < 2 ^ (prefixWord ++ tailWord_472829).sum := by decide
  have hdescent : baseEnd_472829 < baseStart_472829 := by decide
  rcases family_descends (prefixWord ++ tailWord_472829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472836 : List Nat := [2, 3, 2, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_472836 : Nat := 118140960795 + 472836 * 2 ^ 59
def prefixEnd_472836 : Nat := 4983230072969 + 3 ^ 40 * 472836 * 2
def baseEnd_472836 : Nat := 242792138749417260675473

theorem tailTrace_472836 : CollatzResearch.WordTrace tailWord_472836 prefixEnd_472836 242792138749417260675473 := by
  unfold tailWord_472836
  simp only [CollatzResearch.WordTrace]
  refine ⟨8622872857501700402379181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11497163810002267203172241 8622872857501700402379181)
  ·
    refine ⟨3233577321563137650892193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8622872857501700402379181 3233577321563137650892193)
    ·
      refine ⟨2425182991172353238169145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3233577321563137650892193 2425182991172353238169145)
      ·
        refine ⟨1818887243379264928626859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2425182991172353238169145 1818887243379264928626859)
        ·
          refine ⟨2728330865068897392940289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818887243379264928626859 2728330865068897392940289)
          ·
            refine ⟨2046248148801673044705217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2728330865068897392940289 2046248148801673044705217)
            ·
              refine ⟨1534686111601254783528913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2046248148801673044705217 1534686111601254783528913)
              ·
                refine ⟨1151014583700941087646685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1534686111601254783528913 1151014583700941087646685)
                ·
                  refine ⟨431630468887852907867507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1151014583700941087646685 431630468887852907867507)
                  ·
                    refine ⟨647445703331779361801261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 431630468887852907867507 647445703331779361801261)
                    ·
                      refine ⟨242792138749417260675473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 647445703331779361801261 242792138749417260675473)
                      ·
                        rfl

theorem cell23_472836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_472836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472836 prefixEnd_472836 := by exact prefixLift 472836
  have htrace : WordTrace (prefixWord ++ tailWord_472836) baseStart_472836 baseEnd_472836 := by
    simpa [prefixWord, tailWord_472836, baseEnd_472836] using wordTrace_append hprefix tailTrace_472836
  have hstable : (prefixWord ++ tailWord_472836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472836).length < 2 ^ (prefixWord ++ tailWord_472836).sum := by decide
  have hdescent : baseEnd_472836 < baseStart_472836 := by decide
  rcases family_descends (prefixWord ++ tailWord_472836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472853 : List Nat := [1, 3, 2, 1, 2, 3, 3, 3, 1, 1, 3]
def baseStart_472853 : Nat := 118140960795 + 472853 * 2 ^ 59
def prefixEnd_472853 : Nat := 4983230072969 + 3 ^ 40 * 472853 * 2
def baseEnd_472853 : Nat := 242800867920543694162895

theorem tailTrace_472853 : CollatzResearch.WordTrace tailWord_472853 prefixEnd_472853 242800867920543694162895 := by
  unfold tailWord_472853
  simp only [CollatzResearch.WordTrace]
  refine ⟨17246365755941812708127213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11497577170627875138751475 17246365755941812708127213)
  ·
    refine ⟨6467387158478179765547705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17246365755941812708127213 6467387158478179765547705)
    ·
      refine ⟨4850540368858634824160779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6467387158478179765547705 4850540368858634824160779)
      ·
        refine ⟨7275810553287952236241169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4850540368858634824160779 7275810553287952236241169)
        ·
          refine ⟨5456857914965964177180877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7275810553287952236241169 5456857914965964177180877)
          ·
            refine ⟨2046321718112236566442829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5456857914965964177180877 2046321718112236566442829)
            ·
              refine ⟨767370644292088712416061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2046321718112236566442829 767370644292088712416061)
              ·
                refine ⟨287763991609533267156023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 767370644292088712416061 287763991609533267156023)
                ·
                  refine ⟨431645987414299900734035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287763991609533267156023 431645987414299900734035)
                  ·
                    refine ⟨647468981121449851101053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 431645987414299900734035 647468981121449851101053)
                    ·
                      refine ⟨242800867920543694162895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 647468981121449851101053 242800867920543694162895)
                      ·
                        rfl

theorem cell23_472853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 1, 1, 3].length) (baseStart_472853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472853 prefixEnd_472853 := by exact prefixLift 472853
  have htrace : WordTrace (prefixWord ++ tailWord_472853) baseStart_472853 baseEnd_472853 := by
    simpa [prefixWord, tailWord_472853, baseEnd_472853] using wordTrace_append hprefix tailTrace_472853
  have hstable : (prefixWord ++ tailWord_472853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472853).length < 2 ^ (prefixWord ++ tailWord_472853).sum := by decide
  have hdescent : baseEnd_472853 < baseStart_472853 := by decide
  rcases family_descends (prefixWord ++ tailWord_472853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472869 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 4, 4]
def baseStart_472869 : Nat := 118140960795 + 472869 * 2 ^ 59
def prefixEnd_472869 : Nat := 4983230072969 + 3 ^ 40 * 472869 * 2
def baseEnd_472869 : Nat := 80936361203671877187607

theorem tailTrace_472869 : CollatzResearch.WordTrace tailWord_472869 prefixEnd_472869 80936361203671877187607 := by
  unfold tailWord_472869
  simp only [CollatzResearch.WordTrace]
  refine ⟨17246949323883847440709661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11497966215922564960473107 17246949323883847440709661)
  ·
    refine ⟨6467605996456442790266123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17246949323883847440709661 6467605996456442790266123)
    ·
      refine ⟨9701408994684664185399185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6467605996456442790266123 9701408994684664185399185)
      ·
        refine ⟨7276056746013498139049389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9701408994684664185399185 7276056746013498139049389)
        ·
          refine ⟨2728521279755061802143521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7276056746013498139049389 2728521279755061802143521)
          ·
            refine ⟨2046390959816296351607641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2728521279755061802143521 2046390959816296351607641)
            ·
              refine ⟨1534793219862222263705731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2046390959816296351607641 1534793219862222263705731)
              ·
                refine ⟨2302189829793333395558597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534793219862222263705731 2302189829793333395558597)
                ·
                  refine ⟨431660593086250011667237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2302189829793333395558597 431660593086250011667237)
                  ·
                    refine ⟨80936361203671877187607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 431660593086250011667237 80936361203671877187607)
                    ·
                      rfl

theorem cell23_472869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_472869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472869 prefixEnd_472869 := by exact prefixLift 472869
  have htrace : WordTrace (prefixWord ++ tailWord_472869) baseStart_472869 baseEnd_472869 := by
    simpa [prefixWord, tailWord_472869, baseEnd_472869] using wordTrace_append hprefix tailTrace_472869
  have hstable : (prefixWord ++ tailWord_472869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472869).length < 2 ^ (prefixWord ++ tailWord_472869).sum := by decide
  have hdescent : baseEnd_472869 < baseStart_472869 := by decide
  rcases family_descends (prefixWord ++ tailWord_472869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472882 : List Nat := [3, 2, 1, 1, 3, 2, 1, 10]
def baseStart_472882 : Nat := 118140960795 + 472882 * 2 ^ 59
def prefixEnd_472882 : Nat := 4983230072969 + 3 ^ 40 * 472882 * 2
def baseEnd_472882 : Nat := 8993176254056447433343

theorem tailTrace_472882 : CollatzResearch.WordTrace tailWord_472882 prefixEnd_472882 8993176254056447433343 := by
  unfold tailWord_472882
  simp only [CollatzResearch.WordTrace]
  refine ⟨4311855868209187665233225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11498282315224500440621933 4311855868209187665233225)
  ·
    refine ⟨3233891901156890748924919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4311855868209187665233225 3233891901156890748924919)
    ·
      refine ⟨4850837851735336123387379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3233891901156890748924919 4850837851735336123387379)
      ·
        refine ⟨7276256777603004185081069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4850837851735336123387379 7276256777603004185081069)
        ·
          refine ⟨2728596291601126569405401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7276256777603004185081069 2728596291601126569405401)
          ·
            refine ⟨2046447218700844927054051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2728596291601126569405401 2046447218700844927054051)
            ·
              refine ⟨3069670828051267390581077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2046447218700844927054051 3069670828051267390581077)
              ·
                refine ⟨8993176254056447433343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3069670828051267390581077 8993176254056447433343)
                ·
                  rfl

theorem cell23_472882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 10].length) (baseStart_472882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472882 prefixEnd_472882 := by exact prefixLift 472882
  have htrace : WordTrace (prefixWord ++ tailWord_472882) baseStart_472882 baseEnd_472882 := by
    simpa [prefixWord, tailWord_472882, baseEnd_472882] using wordTrace_append hprefix tailTrace_472882
  have hstable : (prefixWord ++ tailWord_472882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472882).length < 2 ^ (prefixWord ++ tailWord_472882).sum := by decide
  have hdescent : baseEnd_472882 < baseStart_472882 := by decide
  rcases family_descends (prefixWord ++ tailWord_472882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472893 : List Nat := [1, 4, 1, 4, 1, 3, 1, 2, 1, 1, 4]
def baseStart_472893 : Nat := 118140960795 + 472893 * 2 ^ 59
def prefixEnd_472893 : Nat := 4983230072969 + 3 ^ 40 * 472893 * 2
def baseEnd_472893 : Nat := 242821407146723537662711

theorem tailTrace_472893 : CollatzResearch.WordTrace tailWord_472893 prefixEnd_472893 242821407146723537662711 := by
  unfold tailWord_472893
  simp only [CollatzResearch.WordTrace]
  refine ⟨17247824675796899539583333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11498549783864599693055555 17247824675796899539583333)
  ·
    refine ⟨3233967126711918663671875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17247824675796899539583333 3233967126711918663671875)
    ·
      refine ⟨4850950690067877995507813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3233967126711918663671875 4850950690067877995507813)
      ·
        refine ⟨909553254387727124157715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4850950690067877995507813 909553254387727124157715)
        ·
          refine ⟨1364329881581590686236573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909553254387727124157715 1364329881581590686236573)
          ·
            refine ⟨511623705593096507338715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1364329881581590686236573 511623705593096507338715)
            ·
              refine ⟨767435558389644761008073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511623705593096507338715 767435558389644761008073)
              ·
                refine ⟨575576668792233570756055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767435558389644761008073 575576668792233570756055)
                ·
                  refine ⟨863365003188350356134083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575576668792233570756055 863365003188350356134083)
                  ·
                    refine ⟨1295047504782525534201125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 863365003188350356134083 1295047504782525534201125)
                    ·
                      refine ⟨242821407146723537662711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1295047504782525534201125 242821407146723537662711)
                      ·
                        rfl

theorem cell23_472893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_472893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472893 prefixEnd_472893 := by exact prefixLift 472893
  have htrace : WordTrace (prefixWord ++ tailWord_472893) baseStart_472893 baseEnd_472893 := by
    simpa [prefixWord, tailWord_472893, baseEnd_472893] using wordTrace_append hprefix tailTrace_472893
  have hstable : (prefixWord ++ tailWord_472893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472893).length < 2 ^ (prefixWord ++ tailWord_472893).sum := by decide
  have hdescent : baseEnd_472893 < baseStart_472893 := by decide
  rcases family_descends (prefixWord ++ tailWord_472893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472913 : List Nat := [1, 2, 2, 1, 5, 2, 3, 1, 1, 2, 3]
def baseStart_472913 : Nat := 118140960795 + 472913 * 2 ^ 59
def prefixEnd_472913 : Nat := 4983230072969 + 3 ^ 40 * 472913 * 2
def baseEnd_472913 : Nat := 242831676759813459412619

theorem tailTrace_472913 : CollatzResearch.WordTrace tailWord_472913 prefixEnd_472913 242831676759813459412619 := by
  unfold tailWord_472913
  simp only [CollatzResearch.WordTrace]
  refine ⟨17248554135724442955311393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11499036090482961970207595 17248554135724442955311393)
  ·
    refine ⟨12936415601793332216483545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17248554135724442955311393 12936415601793332216483545)
    ·
      refine ⟨9702311701344999162362659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12936415601793332216483545 9702311701344999162362659)
      ·
        refine ⟨14553467552017498743543989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9702311701344999162362659 14553467552017498743543989)
        ·
          refine ⟨1364387583001640507207249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14553467552017498743543989 1364387583001640507207249)
          ·
            refine ⟨1023290687251230380405437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1364387583001640507207249 1023290687251230380405437)
            ·
              refine ⟨383734007719211392652039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1023290687251230380405437 383734007719211392652039)
              ·
                refine ⟨575601011578817088978059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383734007719211392652039 575601011578817088978059)
                ·
                  refine ⟨863401517368225633467089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575601011578817088978059 863401517368225633467089)
                  ·
                    refine ⟨647551138026169225100317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 863401517368225633467089 647551138026169225100317)
                    ·
                      refine ⟨242831676759813459412619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 647551138026169225100317 242831676759813459412619)
                      ·
                        rfl

theorem cell23_472913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 1, 2, 3].length) (baseStart_472913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472913 prefixEnd_472913 := by exact prefixLift 472913
  have htrace : WordTrace (prefixWord ++ tailWord_472913) baseStart_472913 baseEnd_472913 := by
    simpa [prefixWord, tailWord_472913, baseEnd_472913] using wordTrace_append hprefix tailTrace_472913
  have hstable : (prefixWord ++ tailWord_472913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472913).length < 2 ^ (prefixWord ++ tailWord_472913).sum := by decide
  have hdescent : baseEnd_472913 < baseStart_472913 := by decide
  rcases family_descends (prefixWord ++ tailWord_472913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472927 : List Nat := [1, 1, 2, 3, 1, 6, 2, 2, 1, 2, 2]
def baseStart_472927 : Nat := 118140960795 + 472927 * 2 ^ 59
def prefixEnd_472927 : Nat := 4983230072969 + 3 ^ 40 * 472927 * 2
def baseEnd_472927 : Nat := 242838865488976404637555

theorem tailTrace_472927 : CollatzResearch.WordTrace tailWord_472927 prefixEnd_472927 242838865488976404637555 := by
  unfold tailWord_472927
  simp only [CollatzResearch.WordTrace]
  refine ⟨17249064757673723346321035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11499376505115815564214023 17249064757673723346321035)
  ·
    refine ⟨25873597136510585019481553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17249064757673723346321035 25873597136510585019481553)
    ·
      refine ⟨19405197852382938764611165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25873597136510585019481553 19405197852382938764611165)
      ·
        refine ⟨7276949194643602036729187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19405197852382938764611165 7276949194643602036729187)
        ·
          refine ⟨10915423791965403055093781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7276949194643602036729187 10915423791965403055093781)
          ·
            refine ⟨511660490248378268207521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10915423791965403055093781 511660490248378268207521)
            ·
              refine ⟨383745367686283701155641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511660490248378268207521 383745367686283701155641)
              ·
                refine ⟨287809025764712775866731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383745367686283701155641 287809025764712775866731)
                ·
                  refine ⟨431713538647069163800097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287809025764712775866731 431713538647069163800097)
                  ·
                    refine ⟨323785153985301872850073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 431713538647069163800097 323785153985301872850073)
                    ·
                      refine ⟨242838865488976404637555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 323785153985301872850073 242838865488976404637555)
                      ·
                        rfl

theorem cell23_472927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 1, 2, 2].length) (baseStart_472927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472927 prefixEnd_472927 := by exact prefixLift 472927
  have htrace : WordTrace (prefixWord ++ tailWord_472927) baseStart_472927 baseEnd_472927 := by
    simpa [prefixWord, tailWord_472927, baseEnd_472927] using wordTrace_append hprefix tailTrace_472927
  have hstable : (prefixWord ++ tailWord_472927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472927).length < 2 ^ (prefixWord ++ tailWord_472927).sum := by decide
  have hdescent : baseEnd_472927 < baseStart_472927 := by decide
  rcases family_descends (prefixWord ++ tailWord_472927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472936 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 5, 3, 2]
def baseStart_472936 : Nat := 118140960795 + 472936 * 2 ^ 59
def prefixEnd_472936 : Nat := 4983230072969 + 3 ^ 40 * 472936 * 2
def baseEnd_472936 : Nat := 242843486814866869425013

theorem tailTrace_472936 : CollatzResearch.WordTrace tailWord_472936 prefixEnd_472936 242843486814866869425013 := by
  unfold tailWord_472936
  simp only [CollatzResearch.WordTrace]
  refine ⟨8624696507320558941699331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11499595343094078588932441 8624696507320558941699331)
  ·
    refine ⟨12937044760980838412548997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8624696507320558941699331 12937044760980838412548997)
    ·
      refine ⟨2425695892683907202352937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12937044760980838412548997 2425695892683907202352937)
      ·
        refine ⟨1819271919512930401764703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2425695892683907202352937 1819271919512930401764703)
        ·
          refine ⟨2728907879269395602647055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1819271919512930401764703 2728907879269395602647055)
          ·
            refine ⟨4093361818904093403970583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728907879269395602647055 4093361818904093403970583)
            ·
              refine ⟨6140042728356140105955875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4093361818904093403970583 6140042728356140105955875)
              ·
                refine ⟨9210064092534210158933813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6140042728356140105955875 9210064092534210158933813)
                ·
                  refine ⟨863443508675082202400045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9210064092534210158933813 863443508675082202400045)
                  ·
                    refine ⟨323791315753155825900017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 863443508675082202400045 323791315753155825900017)
                    ·
                      refine ⟨242843486814866869425013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 323791315753155825900017 242843486814866869425013)
                      ·
                        rfl

theorem cell23_472936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_472936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472936 prefixEnd_472936 := by exact prefixLift 472936
  have htrace : WordTrace (prefixWord ++ tailWord_472936) baseStart_472936 baseEnd_472936 := by
    simpa [prefixWord, tailWord_472936, baseEnd_472936] using wordTrace_append hprefix tailTrace_472936
  have hstable : (prefixWord ++ tailWord_472936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472936).length < 2 ^ (prefixWord ++ tailWord_472936).sum := by decide
  have hdescent : baseEnd_472936 < baseStart_472936 := by decide
  rcases family_descends (prefixWord ++ tailWord_472936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472949 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_472949 : Nat := 118140960795 + 472949 * 2 ^ 59
def prefixEnd_472949 : Nat := 4983230072969 + 3 ^ 40 * 472949 * 2
def baseEnd_472949 : Nat := 242850162063375318562453

theorem tailTrace_472949 : CollatzResearch.WordTrace tailWord_472949 prefixEnd_472949 242850162063375318562453 := by
  unfold tailWord_472949
  simp only [CollatzResearch.WordTrace]
  refine ⟨17249867163594021103621901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11499911442396014069081267 17249867163594021103621901)
  ·
    refine ⟨6468700186347757913858213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17249867163594021103621901 6468700186347757913858213)
    ·
      refine ⟨1212881284940204608848415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6468700186347757913858213 1212881284940204608848415)
      ·
        refine ⟨1819321927410306913272623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1212881284940204608848415 1819321927410306913272623)
        ·
          refine ⟨2728982891115460369908935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1819321927410306913272623 2728982891115460369908935)
          ·
            refine ⟨4093474336673190554863403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728982891115460369908935 4093474336673190554863403)
            ·
              refine ⟨6140211505009785832295105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4093474336673190554863403 6140211505009785832295105)
              ·
                refine ⟨4605158628757339374221329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6140211505009785832295105 4605158628757339374221329)
                ·
                  refine ⟨3453868971568004530665997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4605158628757339374221329 3453868971568004530665997)
                  ·
                    refine ⟨1295200864338001698999749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3453868971568004530665997 1295200864338001698999749)
                    ·
                      refine ⟨242850162063375318562453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1295200864338001698999749 242850162063375318562453)
                      ·
                        rfl

theorem cell23_472949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_472949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472949 prefixEnd_472949 := by exact prefixLift 472949
  have htrace : WordTrace (prefixWord ++ tailWord_472949) baseStart_472949 baseEnd_472949 := by
    simpa [prefixWord, tailWord_472949, baseEnd_472949] using wordTrace_append hprefix tailTrace_472949
  have hstable : (prefixWord ++ tailWord_472949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472949).length < 2 ^ (prefixWord ++ tailWord_472949).sum := by decide
  have hdescent : baseEnd_472949 < baseStart_472949 := by decide
  rcases family_descends (prefixWord ++ tailWord_472949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472970 : List Nat := [3, 1, 2, 4, 2, 1, 1, 3, 1, 3, 2]
def baseStart_472970 : Nat := 118140960795 + 472970 * 2 ^ 59
def prefixEnd_472970 : Nat := 4983230072969 + 3 ^ 40 * 472970 * 2
def baseEnd_472970 : Nat := 242860945157119736399857

theorem tailTrace_472970 : CollatzResearch.WordTrace tailWord_472970 prefixEnd_472970 242860945157119736399857 := by
  unfold tailWord_472970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4312658274129485422534091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11500422064345294460090909 4312658274129485422534091)
  ·
    refine ⟨6468987411194228133801137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4312658274129485422534091 6468987411194228133801137)
    ·
      refine ⟨4851740558395671100350853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6468987411194228133801137 4851740558395671100350853)
      ·
        refine ⟨909701354699188331315785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4851740558395671100350853 909701354699188331315785)
        ·
          refine ⟨682276016024391248486839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 909701354699188331315785 682276016024391248486839)
          ·
            refine ⟨1023414024036586872730259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682276016024391248486839 1023414024036586872730259)
            ·
              refine ⟨1535121036054880309095389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023414024036586872730259 1535121036054880309095389)
              ·
                refine ⟨575670388520580115910771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1535121036054880309095389 575670388520580115910771)
                ·
                  refine ⟨863505582780870173866157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575670388520580115910771 863505582780870173866157)
                  ·
                    refine ⟨323814593542826315199809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 863505582780870173866157 323814593542826315199809)
                    ·
                      refine ⟨242860945157119736399857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 323814593542826315199809 242860945157119736399857)
                      ·
                        rfl

theorem cell23_472970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_472970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472970 prefixEnd_472970 := by exact prefixLift 472970
  have htrace : WordTrace (prefixWord ++ tailWord_472970) baseStart_472970 baseEnd_472970 := by
    simpa [prefixWord, tailWord_472970, baseEnd_472970] using wordTrace_append hprefix tailTrace_472970
  have hstable : (prefixWord ++ tailWord_472970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472970).length < 2 ^ (prefixWord ++ tailWord_472970).sum := by decide
  have hdescent : baseEnd_472970 < baseStart_472970 := by decide
  rcases family_descends (prefixWord ++ tailWord_472970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472972 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 11]
def baseStart_472972 : Nat := 118140960795 + 472972 * 2 ^ 59
def prefixEnd_472972 : Nat := 4983230072969 + 3 ^ 40 * 472972 * 2
def baseEnd_472972 : Nat := 26984663568714303174983

theorem tailTrace_472972 : CollatzResearch.WordTrace tailWord_472972 prefixEnd_472972 26984663568714303174983 := by
  unfold tailWord_472972
  simp only [CollatzResearch.WordTrace]
  refine ⟨8625353021255348015854585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11500470695007130687806113 8625353021255348015854585)
  ·
    refine ⟨6469014765941511011890939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8625353021255348015854585 6469014765941511011890939)
    ·
      refine ⟨9703522148912266517836409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6469014765941511011890939 9703522148912266517836409)
      ·
        refine ⟨7277641611684199888377307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9703522148912266517836409 7277641611684199888377307)
        ·
          refine ⟨10916462417526299832565961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7277641611684199888377307 10916462417526299832565961)
          ·
            refine ⟨8187346813144724874424471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10916462417526299832565961 8187346813144724874424471)
            ·
              refine ⟨12281020219717087311636707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8187346813144724874424471 12281020219717087311636707)
              ·
                refine ⟨18421530329575630967455061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12281020219717087311636707 18421530329575630967455061)
                ·
                  refine ⟨26984663568714303174983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 18421530329575630967455061 26984663568714303174983)
                  ·
                    rfl

theorem cell23_472972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 11].length) (baseStart_472972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472972 prefixEnd_472972 := by exact prefixLift 472972
  have htrace : WordTrace (prefixWord ++ tailWord_472972) baseStart_472972 baseEnd_472972 := by
    simpa [prefixWord, tailWord_472972, baseEnd_472972] using wordTrace_append hprefix tailTrace_472972
  have hstable : (prefixWord ++ tailWord_472972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472972).length < 2 ^ (prefixWord ++ tailWord_472972).sum := by decide
  have hdescent : baseEnd_472972 < baseStart_472972 := by decide
  rcases family_descends (prefixWord ++ tailWord_472972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472983 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 4, 2, 2]
def baseStart_472983 : Nat := 118140960795 + 472983 * 2 ^ 59
def prefixEnd_472983 : Nat := 4983230072969 + 3 ^ 40 * 472983 * 2
def baseEnd_472983 : Nat := 242867620405628185537297

theorem tailTrace_472983 : CollatzResearch.WordTrace tailWord_472983 prefixEnd_472983 242867620405628185537297 := by
  unfold tailWord_472983
  simp only [CollatzResearch.WordTrace]
  refine ⟨17251107245470844910359603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11500738163647229940239735 17251107245470844910359603)
  ·
    refine ⟨25876660868206267365539405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17251107245470844910359603 25876660868206267365539405)
    ·
      refine ⟨9703747825577350262077277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25876660868206267365539405 9703747825577350262077277)
      ·
        refine ⟨3638905434591506348278979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9703747825577350262077277 3638905434591506348278979)
        ·
          refine ⟨5458358151887259522418469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3638905434591506348278979 5458358151887259522418469)
          ·
            refine ⟨1023442153478861160453463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5458358151887259522418469 1023442153478861160453463)
            ·
              refine ⟨1535163230218291740680195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023442153478861160453463 1535163230218291740680195)
              ·
                refine ⟨2302744845327437611020293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535163230218291740680195 2302744845327437611020293)
                ·
                  refine ⟨431764658498894552066305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2302744845327437611020293 431764658498894552066305)
                  ·
                    refine ⟨323823493874170914049729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 431764658498894552066305 323823493874170914049729)
                    ·
                      refine ⟨242867620405628185537297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 323823493874170914049729 242867620405628185537297)
                      ·
                        rfl

theorem cell23_472983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_472983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472983 prefixEnd_472983 := by exact prefixLift 472983
  have htrace : WordTrace (prefixWord ++ tailWord_472983) baseStart_472983 baseEnd_472983 := by
    simpa [prefixWord, tailWord_472983, baseEnd_472983] using wordTrace_append hprefix tailTrace_472983
  have hstable : (prefixWord ++ tailWord_472983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472983).length < 2 ^ (prefixWord ++ tailWord_472983).sum := by decide
  have hdescent : baseEnd_472983 < baseStart_472983 := by decide
  rcases family_descends (prefixWord ++ tailWord_472983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472989 : List Nat := [1, 4, 2, 1, 2, 2, 1, 3, 7]
def baseStart_472989 : Nat := 118140960795 + 472989 * 2 ^ 59
def prefixEnd_472989 : Nat := 4983230072969 + 3 ^ 40 * 472989 * 2
def baseEnd_472989 : Nat := 26985633476617240229141

theorem tailTrace_472989 : CollatzResearch.WordTrace tailWord_472989 prefixEnd_472989 26985633476617240229141 := by
  unfold tailWord_472989
  simp only [CollatzResearch.WordTrace]
  refine ⟨17251326083449107935078021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11500884055632738623385347 17251326083449107935078021)
  ·
    refine ⟨3234623640646707737827129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17251326083449107935078021 3234623640646707737827129)
    ·
      refine ⟨2425967730485030803370347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3234623640646707737827129 2425967730485030803370347)
      ·
        refine ⟨3638951595727546205055521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2425967730485030803370347 3638951595727546205055521)
        ·
          refine ⟨2729213696795659653791641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3638951595727546205055521 2729213696795659653791641)
          ·
            refine ⟨2046910272596744740343731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2729213696795659653791641 2046910272596744740343731)
            ·
              refine ⟨3070365408895117110515597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2046910272596744740343731 3070365408895117110515597)
              ·
                refine ⟨1151387028335668916443349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3070365408895117110515597 1151387028335668916443349)
                ·
                  refine ⟨26985633476617240229141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1151387028335668916443349 26985633476617240229141)
                  ·
                    rfl

theorem cell23_472989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_472989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_472989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_472989 prefixEnd_472989 := by exact prefixLift 472989
  have htrace : WordTrace (prefixWord ++ tailWord_472989) baseStart_472989 baseEnd_472989 := by
    simpa [prefixWord, tailWord_472989, baseEnd_472989] using wordTrace_append hprefix tailTrace_472989
  have hstable : (prefixWord ++ tailWord_472989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472989).length < 2 ^ (prefixWord ++ tailWord_472989).sum := by decide
  have hdescent : baseEnd_472989 < baseStart_472989 := by decide
  rcases family_descends (prefixWord ++ tailWord_472989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473036 : List Nat := [2, 2, 1, 4, 1, 3, 1, 2, 2, 5]
def baseStart_473036 : Nat := 118140960795 + 473036 * 2 ^ 59
def prefixEnd_473036 : Nat := 4983230072969 + 3 ^ 40 * 473036 * 2
def baseEnd_473036 : Nat := 80964944960105492724851

theorem tailTrace_473036 : CollatzResearch.WordTrace tailWord_473036 prefixEnd_473036 80964944960105492724851 := by
  unfold tailWord_473036
  simp only [CollatzResearch.WordTrace]
  refine ⟨8626520157139417481019481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11502026876185889974692641 8626520157139417481019481)
  ·
    refine ⟨6469890117854563110764611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8626520157139417481019481 6469890117854563110764611)
    ·
      refine ⟨9704835176781844666146917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6469890117854563110764611 9704835176781844666146917)
      ·
        refine ⟨1819656595646595874902547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9704835176781844666146917 1819656595646595874902547)
        ·
          refine ⟨2729484893469893812353821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1819656595646595874902547 2729484893469893812353821)
          ·
            refine ⟨1023556835051210179632683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2729484893469893812353821 1023556835051210179632683)
            ·
              refine ⟨1535335252576815269449025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023556835051210179632683 1535335252576815269449025)
              ·
                refine ⟨1151501439432611452086769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1535335252576815269449025 1151501439432611452086769)
                ·
                  refine ⟨863626079574458589065077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1151501439432611452086769 863626079574458589065077)
                  ·
                    refine ⟨80964944960105492724851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 863626079574458589065077 80964944960105492724851)
                    ·
                      rfl

theorem cell23_473036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_473036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473036 prefixEnd_473036 := by exact prefixLift 473036
  have htrace : WordTrace (prefixWord ++ tailWord_473036) baseStart_473036 baseEnd_473036 := by
    simpa [prefixWord, tailWord_473036, baseEnd_473036] using wordTrace_append hprefix tailTrace_473036
  have hstable : (prefixWord ++ tailWord_473036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473036).length < 2 ^ (prefixWord ++ tailWord_473036).sum := by decide
  have hdescent : baseEnd_473036 < baseStart_473036 := by decide
  rcases family_descends (prefixWord ++ tailWord_473036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473056 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 2, 4, 2]
def baseStart_473056 : Nat := 118140960795 + 473056 * 2 ^ 59
def prefixEnd_473056 : Nat := 4983230072969 + 3 ^ 40 * 473056 * 2
def baseEnd_473056 : Nat := 242905104493406399924461

theorem tailTrace_473056 : CollatzResearch.WordTrace tailWord_473056 prefixEnd_473056 242905104493406399924461 := by
  unfold tailWord_473056
  simp only [CollatzResearch.WordTrace]
  refine ⟨8626884887103189188883511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11502513182804252251844681 8626884887103189188883511)
  ·
    refine ⟨12940327330654783783325267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8626884887103189188883511 12940327330654783783325267)
    ·
      refine ⟨19410490995982175674987901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12940327330654783783325267 19410490995982175674987901)
      ·
        refine ⟨7278934123493315878120463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19410490995982175674987901 7278934123493315878120463)
        ·
          refine ⟨10918401185239973817180695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7278934123493315878120463 10918401185239973817180695)
          ·
            refine ⟨16377601777859960725771043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10918401185239973817180695 16377601777859960725771043)
            ·
              refine ⟨24566402666789941088656565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16377601777859960725771043 24566402666789941088656565)
              ·
                refine ⟨2303100250011556977061553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24566402666789941088656565 2303100250011556977061553)
                ·
                  refine ⟨1727325187508667732796165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2303100250011556977061553 1727325187508667732796165)
                  ·
                    refine ⟨323873472657875199899281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1727325187508667732796165 323873472657875199899281)
                    ·
                      refine ⟨242905104493406399924461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 323873472657875199899281 242905104493406399924461)
                      ·
                        rfl

theorem cell23_473056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_473056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473056 prefixEnd_473056 := by exact prefixLift 473056
  have htrace : WordTrace (prefixWord ++ tailWord_473056) baseStart_473056 baseEnd_473056 := by
    simpa [prefixWord, tailWord_473056, baseEnd_473056] using wordTrace_append hprefix tailTrace_473056
  have hstable : (prefixWord ++ tailWord_473056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473056).length < 2 ^ (prefixWord ++ tailWord_473056).sum := by decide
  have hdescent : baseEnd_473056 < baseStart_473056 := by decide
  rcases family_descends (prefixWord ++ tailWord_473056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473066 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 5, 4]
def baseStart_473066 : Nat := 118140960795 + 473066 * 2 ^ 59
def prefixEnd_473066 : Nat := 4983230072969 + 3 ^ 40 * 473066 * 2
def baseEnd_473066 : Nat := 80970079766650453599805

theorem tailTrace_473066 : CollatzResearch.WordTrace tailWord_473066 prefixEnd_473066 80970079766650453599805 := by
  unfold tailWord_473066
  simp only [CollatzResearch.WordTrace]
  refine ⟨4313533626042537521407763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11502756336113433390420701 4313533626042537521407763)
  ·
    refine ⟨6470300439063806282111645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4313533626042537521407763 6470300439063806282111645)
    ·
      refine ⟨2426362664648927355791867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6470300439063806282111645 2426362664648927355791867)
      ·
        refine ⟨3639543996973391033687801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2426362664648927355791867 3639543996973391033687801)
        ·
          refine ⟨2729657997730043275265851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3639543996973391033687801 2729657997730043275265851)
          ·
            refine ⟨4094486996595064912898777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2729657997730043275265851 4094486996595064912898777)
            ·
              refine ⟨3070865247446298684674083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4094486996595064912898777 3070865247446298684674083)
              ·
                refine ⟨4606297871169448027011125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3070865247446298684674083 4606297871169448027011125)
                ·
                  refine ⟨431840425422135752532293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4606297871169448027011125 431840425422135752532293)
                  ·
                    refine ⟨80970079766650453599805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 431840425422135752532293 80970079766650453599805)
                    ·
                      rfl

theorem cell23_473066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_473066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473066 prefixEnd_473066 := by exact prefixLift 473066
  have htrace : WordTrace (prefixWord ++ tailWord_473066) baseStart_473066 baseEnd_473066 := by
    simpa [prefixWord, tailWord_473066, baseEnd_473066] using wordTrace_append hprefix tailTrace_473066
  have hstable : (prefixWord ++ tailWord_473066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473066).length < 2 ^ (prefixWord ++ tailWord_473066).sum := by decide
  have hdescent : baseEnd_473066 < baseStart_473066 := by decide
  rcases family_descends (prefixWord ++ tailWord_473066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473073 : List Nat := [1, 2, 2, 2, 5, 1, 2, 1, 2, 1, 4]
def baseStart_473073 : Nat := 118140960795 + 473073 * 2 ^ 59
def prefixEnd_473073 : Nat := 4983230072969 + 3 ^ 40 * 473073 * 2
def baseEnd_473073 : Nat := 242913833664532833411883

theorem tailTrace_473073 : CollatzResearch.WordTrace tailWord_473073 prefixEnd_473073 242913833664532833411883 := by
  unfold tailWord_473073
  simp only [CollatzResearch.WordTrace]
  refine ⟨17254389815144790281135873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11502926543429860187423915 17254389815144790281135873)
  ·
    refine ⟨12940792361358592710851905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17254389815144790281135873 12940792361358592710851905)
    ·
      refine ⟨9705594271018944533138929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12940792361358592710851905 9705594271018944533138929)
      ·
        refine ⟨7279195703264208399854197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9705594271018944533138929 7279195703264208399854197)
        ·
          refine ⟨682424597181019537486331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7279195703264208399854197 682424597181019537486331)
          ·
            refine ⟨1023636895771529306229497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682424597181019537486331 1023636895771529306229497)
            ·
              refine ⟨767727671828646979672123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1023636895771529306229497 767727671828646979672123)
              ·
                refine ⟨1151591507742970469508185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767727671828646979672123 1151591507742970469508185)
                ·
                  refine ⟨863693630807227852131139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1151591507742970469508185 863693630807227852131139)
                  ·
                    refine ⟨1295540446210841778196709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 863693630807227852131139 1295540446210841778196709)
                    ·
                      refine ⟨242913833664532833411883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1295540446210841778196709 242913833664532833411883)
                      ·
                        rfl

theorem cell23_473073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_473073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473073 prefixEnd_473073 := by exact prefixLift 473073
  have htrace : WordTrace (prefixWord ++ tailWord_473073) baseStart_473073 baseEnd_473073 := by
    simpa [prefixWord, tailWord_473073, baseEnd_473073] using wordTrace_append hprefix tailTrace_473073
  have hstable : (prefixWord ++ tailWord_473073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473073).length < 2 ^ (prefixWord ++ tailWord_473073).sum := by decide
  have hdescent : baseEnd_473073 < baseStart_473073 := by decide
  rcases family_descends (prefixWord ++ tailWord_473073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473096 : List Nat := [2, 1, 3, 2, 1, 2, 4, 2, 6]
def baseStart_473096 : Nat := 118140960795 + 473096 * 2 ^ 59
def prefixEnd_473096 : Nat := 4983230072969 + 3 ^ 40 * 473096 * 2
def baseEnd_473096 : Nat := 26991738191065138158253

theorem tailTrace_473096 : CollatzResearch.WordTrace tailWord_473096 prefixEnd_473096 26991738191065138158253 := by
  unfold tailWord_473096
  simp only [CollatzResearch.WordTrace]
  refine ⟨8627614347030732604611571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11503485796040976806148761 8627614347030732604611571)
  ·
    refine ⟨12941421520546098906917357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8627614347030732604611571 12941421520546098906917357)
    ·
      refine ⟨4853033070204787090094009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12941421520546098906917357 4853033070204787090094009)
      ·
        refine ⟨3639774802653590317570507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4853033070204787090094009 3639774802653590317570507)
        ·
          refine ⟨5459662203980385476355761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3639774802653590317570507 5459662203980385476355761)
          ·
            refine ⟨4094746652985289107266821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5459662203980385476355761 4094746652985289107266821)
            ·
              refine ⟨767764997434741707612529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4094746652985289107266821 767764997434741707612529)
              ·
                refine ⟨575823748076056280709397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767764997434741707612529 575823748076056280709397)
                ·
                  refine ⟨26991738191065138158253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 575823748076056280709397 26991738191065138158253)
                  ·
                    rfl

theorem cell23_473096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 6].length) (baseStart_473096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473096 prefixEnd_473096 := by exact prefixLift 473096
  have htrace : WordTrace (prefixWord ++ tailWord_473096) baseStart_473096 baseEnd_473096 := by
    simpa [prefixWord, tailWord_473096, baseEnd_473096] using wordTrace_append hprefix tailTrace_473096
  have hstable : (prefixWord ++ tailWord_473096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473096).length < 2 ^ (prefixWord ++ tailWord_473096).sum := by decide
  have hdescent : baseEnd_473096 < baseStart_473096 := by decide
  rcases family_descends (prefixWord ++ tailWord_473096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473099 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 6]
def baseStart_473099 : Nat := 118140960795 + 473099 * 2 ^ 59
def prefixEnd_473099 : Nat := 4983230072969 + 3 ^ 40 * 473099 * 2
def baseEnd_473099 : Nat := 242927184161549731686763

theorem tailTrace_473099 : CollatzResearch.WordTrace tailWord_473099 prefixEnd_473099 242927184161549731686763 := by
  unfold tailWord_473099
  simp only [CollatzResearch.WordTrace]
  refine ⟨17255338113050596721582351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11503558742033731147721567 17255338113050596721582351)
  ·
    refine ⟨25883007169575895082373527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17255338113050596721582351 25883007169575895082373527)
    ·
      refine ⟨38824510754363842623560291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25883007169575895082373527 38824510754363842623560291)
      ·
        refine ⟨58236766131545763935340437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38824510754363842623560291 58236766131545763935340437)
        ·
          refine ⟨2729848412416207684469083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58236766131545763935340437 2729848412416207684469083)
          ·
            refine ⟨4094772618624311526703625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2729848412416207684469083 4094772618624311526703625)
            ·
              refine ⟨3071079463968233645027719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4094772618624311526703625 3071079463968233645027719)
              ·
                refine ⟨4606619195952350467541579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3071079463968233645027719 4606619195952350467541579)
                ·
                  refine ⟨6909928793928525701312369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4606619195952350467541579 6909928793928525701312369)
                  ·
                    refine ⟨5182446595446394275984277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6909928793928525701312369 5182446595446394275984277)
                    ·
                      refine ⟨242927184161549731686763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5182446595446394275984277 242927184161549731686763)
                      ·
                        rfl

theorem cell23_473099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 6].length) (baseStart_473099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473099 prefixEnd_473099 := by exact prefixLift 473099
  have htrace : WordTrace (prefixWord ++ tailWord_473099) baseStart_473099 baseEnd_473099 := by
    simpa [prefixWord, tailWord_473099, baseEnd_473099] using wordTrace_append hprefix tailTrace_473099
  have hstable : (prefixWord ++ tailWord_473099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473099).length < 2 ^ (prefixWord ++ tailWord_473099).sum := by decide
  have hdescent : baseEnd_473099 < baseStart_473099 := by decide
  rcases family_descends (prefixWord ++ tailWord_473099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473119 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 7]
def baseStart_473119 : Nat := 118140960795 + 473119 * 2 ^ 59
def prefixEnd_473119 : Nat := 4983230072969 + 3 ^ 40 * 473119 * 2
def baseEnd_473119 : Nat := 242937453774639653436671

theorem tailTrace_473119 : CollatzResearch.WordTrace tailWord_473119 prefixEnd_473119 242937453774639653436671 := by
  unfold tailWord_473119
  simp only [CollatzResearch.WordTrace]
  refine ⟨17256067572978140137310411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11504045048652093424873607 17256067572978140137310411)
  ·
    refine ⟨25884101359467210205965617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17256067572978140137310411 25884101359467210205965617)
    ·
      refine ⟨19413076019600407654474213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25884101359467210205965617 19413076019600407654474213)
      ·
        refine ⟨3639951753675076435213915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19413076019600407654474213 3639951753675076435213915)
        ·
          refine ⟨5459927630512614652820873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3639951753675076435213915 5459927630512614652820873)
          ·
            refine ⟨4094945722884460989615655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5459927630512614652820873 4094945722884460989615655)
            ·
              refine ⟨6142418584326691484423483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4094945722884460989615655 6142418584326691484423483)
              ·
                refine ⟨9213627876490037226635225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6142418584326691484423483 9213627876490037226635225)
                ·
                  refine ⟨6910220907367527919976419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9213627876490037226635225 6910220907367527919976419)
                  ·
                    refine ⟨10365331361051291879964629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6910220907367527919976419 10365331361051291879964629)
                    ·
                      refine ⟨242937453774639653436671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10365331361051291879964629 242937453774639653436671)
                      ·
                        rfl

theorem cell23_473119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_473119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473119 prefixEnd_473119 := by exact prefixLift 473119
  have htrace : WordTrace (prefixWord ++ tailWord_473119) baseStart_473119 baseEnd_473119 := by
    simpa [prefixWord, tailWord_473119, baseEnd_473119] using wordTrace_append hprefix tailTrace_473119
  have hstable : (prefixWord ++ tailWord_473119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473119).length < 2 ^ (prefixWord ++ tailWord_473119).sum := by decide
  have hdescent : baseEnd_473119 < baseStart_473119 := by decide
  rcases family_descends (prefixWord ++ tailWord_473119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473123 : List Nat := [1, 1, 1, 4, 3, 1, 3, 2, 3, 1, 3]
def baseStart_473123 : Nat := 118140960795 + 473123 * 2 ^ 59
def prefixEnd_473123 : Nat := 4983230072969 + 3 ^ 40 * 473123 * 2
def baseEnd_473123 : Nat := 242939507697257637786653

theorem tailTrace_473123 : CollatzResearch.WordTrace tailWord_473123 prefixEnd_473123 242939507697257637786653 := by
  unfold tailWord_473123
  simp only [CollatzResearch.WordTrace]
  refine ⟨17256213464963648820456023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11504142309975765880304015 17256213464963648820456023)
  ·
    refine ⟨25884320197445473230684035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17256213464963648820456023 25884320197445473230684035)
    ·
      refine ⟨38826480296168209846026053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25884320197445473230684035 38826480296168209846026053)
      ·
        refine ⟨7279965055531539346129885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38826480296168209846026053 7279965055531539346129885)
        ·
          refine ⟨2729986895824327254798707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7279965055531539346129885 2729986895824327254798707)
          ·
            refine ⟨4094980343736490882198061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2729986895824327254798707 4094980343736490882198061)
            ·
              refine ⟨1535617628901184080824273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4094980343736490882198061 1535617628901184080824273)
              ·
                refine ⟨1151713221675888060618205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1535617628901184080824273 1151713221675888060618205)
                ·
                  refine ⟨431892458128458022731827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1151713221675888060618205 431892458128458022731827)
                  ·
                    refine ⟨647838687192687034097741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 431892458128458022731827 647838687192687034097741)
                    ·
                      refine ⟨242939507697257637786653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 647838687192687034097741 242939507697257637786653)
                      ·
                        rfl

theorem cell23_473123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_473123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473123 prefixEnd_473123 := by exact prefixLift 473123
  have htrace : WordTrace (prefixWord ++ tailWord_473123) baseStart_473123 baseEnd_473123 := by
    simpa [prefixWord, tailWord_473123, baseEnd_473123] using wordTrace_append hprefix tailTrace_473123
  have hstable : (prefixWord ++ tailWord_473123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473123).length < 2 ^ (prefixWord ++ tailWord_473123).sum := by decide
  have hdescent : baseEnd_473123 < baseStart_473123 := by decide
  rcases family_descends (prefixWord ++ tailWord_473123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473127 : List Nat := [1, 1, 7, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_473127 : Nat := 118140960795 + 473127 * 2 ^ 59
def prefixEnd_473127 : Nat := 4983230072969 + 3 ^ 40 * 473127 * 2
def baseEnd_473127 : Nat := 242941561619875622136635

theorem tailTrace_473127 : CollatzResearch.WordTrace tailWord_473127 prefixEnd_473127 242941561619875622136635 := by
  unfold tailWord_473127
  simp only [CollatzResearch.WordTrace]
  refine ⟨17256359356949157503601635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11504239571299438335734423 17256359356949157503601635)
  ·
    refine ⟨25884539035423736255402453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17256359356949157503601635 25884539035423736255402453)
    ·
      refine ⟨606668883642743818485995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 25884539035423736255402453 606668883642743818485995)
      ·
        refine ⟨910003325464115727728993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606668883642743818485995 910003325464115727728993)
        ·
          refine ⟨682502494098086795796745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 910003325464115727728993 682502494098086795796745)
          ·
            refine ⟨511876870573565096847559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682502494098086795796745 511876870573565096847559)
            ·
              refine ⟨767815305860347645271339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511876870573565096847559 767815305860347645271339)
              ·
                refine ⟨1151722958790521467907009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767815305860347645271339 1151722958790521467907009)
                ·
                  refine ⟨863792219092891100930257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1151722958790521467907009 863792219092891100930257)
                  ·
                    refine ⟨647844164319668325697693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 863792219092891100930257 647844164319668325697693)
                    ·
                      refine ⟨242941561619875622136635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 647844164319668325697693 242941561619875622136635)
                      ·
                        rfl

theorem cell23_473127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_473127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473127 prefixEnd_473127 := by exact prefixLift 473127
  have htrace : WordTrace (prefixWord ++ tailWord_473127) baseStart_473127 baseEnd_473127 := by
    simpa [prefixWord, tailWord_473127, baseEnd_473127] using wordTrace_append hprefix tailTrace_473127
  have hstable : (prefixWord ++ tailWord_473127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473127).length < 2 ^ (prefixWord ++ tailWord_473127).sum := by decide
  have hdescent : baseEnd_473127 < baseStart_473127 := by decide
  rcases family_descends (prefixWord ++ tailWord_473127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473143 : List Nat := [1, 1, 3, 1, 2, 2, 6, 1, 1, 5]
def baseStart_473143 : Nat := 118140960795 + 473143 * 2 ^ 59
def prefixEnd_473143 : Nat := 4983230072969 + 3 ^ 40 * 473143 * 2
def baseEnd_473143 : Nat := 80983259103449186512187

theorem tailTrace_473143 : CollatzResearch.WordTrace tailWord_473143 prefixEnd_473143 80983259103449186512187 := by
  unfold tailWord_473143
  simp only [CollatzResearch.WordTrace]
  refine ⟨17256942924891192236184083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11504628616594128157456055 17256942924891192236184083)
  ·
    refine ⟨25885414387336788354276125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17256942924891192236184083 25885414387336788354276125)
    ·
      refine ⟨9707030395251295632853547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25885414387336788354276125 9707030395251295632853547)
      ·
        refine ⟨14560545592876943449280321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9707030395251295632853547 14560545592876943449280321)
        ·
          refine ⟨10920409194657707586960241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14560545592876943449280321 10920409194657707586960241)
          ·
            refine ⟨8190306895993280690220181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10920409194657707586960241 8190306895993280690220181)
            ·
              refine ⟨383920635749685032354071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8190306895993280690220181 383920635749685032354071)
              ·
                refine ⟨575880953624527548531107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383920635749685032354071 575880953624527548531107)
                ·
                  refine ⟨863821430436791322796661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575880953624527548531107 863821430436791322796661)
                  ·
                    refine ⟨80983259103449186512187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 863821430436791322796661 80983259103449186512187)
                    ·
                      rfl

theorem cell23_473143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 1, 5].length) (baseStart_473143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473143 prefixEnd_473143 := by exact prefixLift 473143
  have htrace : WordTrace (prefixWord ++ tailWord_473143) baseStart_473143 baseEnd_473143 := by
    simpa [prefixWord, tailWord_473143, baseEnd_473143] using wordTrace_append hprefix tailTrace_473143
  have hstable : (prefixWord ++ tailWord_473143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473143).length < 2 ^ (prefixWord ++ tailWord_473143).sum := by decide
  have hdescent : baseEnd_473143 < baseStart_473143 := by decide
  rcases family_descends (prefixWord ++ tailWord_473143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473163 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 7, 2, 2]
def baseStart_473163 : Nat := 118140960795 + 473163 * 2 ^ 59
def prefixEnd_473163 : Nat := 4983230072969 + 3 ^ 40 * 473163 * 2
def baseEnd_473163 : Nat := 242960046923437481286469

theorem tailTrace_473163 : CollatzResearch.WordTrace tailWord_473163 prefixEnd_473163 242960046923437481286469 := by
  unfold tailWord_473163
  simp only [CollatzResearch.WordTrace]
  refine ⟨17257672384818735651912143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11505114923212490434608095 17257672384818735651912143)
  ·
    refine ⟨25886508577228103477868215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17257672384818735651912143 25886508577228103477868215)
    ·
      refine ⟨38829762865842155216802323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25886508577228103477868215 38829762865842155216802323)
      ·
        refine ⟨58244644298763232825203485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38829762865842155216802323 58244644298763232825203485)
        ·
          refine ⟨21841741612036212309451307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58244644298763232825203485 21841741612036212309451307)
          ·
            refine ⟨32762612418054318464176961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21841741612036212309451307 32762612418054318464176961)
            ·
              refine ⟨24571959313540738848132721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32762612418054318464176961 24571959313540738848132721)
              ·
                refine ⟨18428969485155554136099541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24571959313540738848132721 18428969485155554136099541)
                ·
                  refine ⟨431928972308333300064833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18428969485155554136099541 431928972308333300064833)
                  ·
                    refine ⟨323946729231249975048625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 431928972308333300064833 323946729231249975048625)
                    ·
                      refine ⟨242960046923437481286469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 323946729231249975048625 242960046923437481286469)
                      ·
                        rfl

theorem cell23_473163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 2, 2].length) (baseStart_473163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473163 prefixEnd_473163 := by exact prefixLift 473163
  have htrace : WordTrace (prefixWord ++ tailWord_473163) baseStart_473163 baseEnd_473163 := by
    simpa [prefixWord, tailWord_473163, baseEnd_473163] using wordTrace_append hprefix tailTrace_473163
  have hstable : (prefixWord ++ tailWord_473163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473163).length < 2 ^ (prefixWord ++ tailWord_473163).sum := by decide
  have hdescent : baseEnd_473163 < baseStart_473163 := by decide
  rcases family_descends (prefixWord ++ tailWord_473163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473166 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_473166 : Nat := 118140960795 + 473166 * 2 ^ 59
def prefixEnd_473166 : Nat := 4983230072969 + 3 ^ 40 * 473166 * 2
def baseEnd_473166 : Nat := 242961587365400969548955

theorem tailTrace_473166 : CollatzResearch.WordTrace tailWord_473166 prefixEnd_473166 242961587365400969548955 := by
  unfold tailWord_473166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2157222725475983395533919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11505187869205244776180901 2157222725475983395533919)
  ·
    refine ⟨3235834088213975093300879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2157222725475983395533919 3235834088213975093300879)
    ·
      refine ⟨4853751132320962639951319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3235834088213975093300879 4853751132320962639951319)
      ·
        refine ⟨7280626698481443959926979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4853751132320962639951319 7280626698481443959926979)
        ·
          refine ⟨10920940047722165939890469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7280626698481443959926979 10920940047722165939890469)
          ·
            refine ⟨2047676258947906113729463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10920940047722165939890469 2047676258947906113729463)
            ·
              refine ⟨3071514388421859170594195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2047676258947906113729463 3071514388421859170594195)
              ·
                refine ⟨4607271582632788755891293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3071514388421859170594195 4607271582632788755891293)
                ·
                  refine ⟨1727726843487295783459235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4607271582632788755891293 1727726843487295783459235)
                  ·
                    refine ⟨2591590265230943675188853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1727726843487295783459235 2591590265230943675188853)
                    ·
                      refine ⟨242961587365400969548955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2591590265230943675188853 242961587365400969548955)
                      ·
                        rfl

theorem cell23_473166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_473166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473166 prefixEnd_473166 := by exact prefixLift 473166
  have htrace : WordTrace (prefixWord ++ tailWord_473166) baseStart_473166 baseEnd_473166 := by
    simpa [prefixWord, tailWord_473166, baseEnd_473166] using wordTrace_append hprefix tailTrace_473166
  have hstable : (prefixWord ++ tailWord_473166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473166).length < 2 ^ (prefixWord ++ tailWord_473166).sum := by decide
  have hdescent : baseEnd_473166 < baseStart_473166 := by decide
  rcases family_descends (prefixWord ++ tailWord_473166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473169 : List Nat := [1, 2, 2, 1, 3, 1, 1, 12]
def baseStart_473169 : Nat := 118140960795 + 473169 * 2 ^ 59
def prefixEnd_473169 : Nat := 4983230072969 + 3 ^ 40 * 473169 * 2
def baseEnd_473169 : Nat := 8998634363235720659683

theorem tailTrace_473169 : CollatzResearch.WordTrace tailWord_473169 prefixEnd_473169 8998634363235720659683 := by
  unfold tailWord_473169
  simp only [CollatzResearch.WordTrace]
  refine ⟨17257891222796998676630561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11505260815197999117753707 17257891222796998676630561)
  ·
    refine ⟨12943418417097749007472921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17257891222796998676630561 12943418417097749007472921)
    ·
      refine ⟨9707563812823311755604691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12943418417097749007472921 9707563812823311755604691)
      ·
        refine ⟨14561345719234967633407037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9707563812823311755604691 14561345719234967633407037)
        ·
          refine ⟨5460504644713112862527639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14561345719234967633407037 5460504644713112862527639)
          ·
            refine ⟨8190756967069669293791459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5460504644713112862527639 8190756967069669293791459)
            ·
              refine ⟨12286135450604503940687189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8190756967069669293791459 12286135450604503940687189)
              ·
                refine ⟨8998634363235720659683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 12286135450604503940687189 8998634363235720659683)
                ·
                  rfl

theorem cell23_473169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 12].length) (baseStart_473169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473169 prefixEnd_473169 := by exact prefixLift 473169
  have htrace : WordTrace (prefixWord ++ tailWord_473169) baseStart_473169 baseEnd_473169 := by
    simpa [prefixWord, tailWord_473169, baseEnd_473169] using wordTrace_append hprefix tailTrace_473169
  have hstable : (prefixWord ++ tailWord_473169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473169).length < 2 ^ (prefixWord ++ tailWord_473169).sum := by decide
  have hdescent : baseEnd_473169 < baseStart_473169 := by decide
  rcases family_descends (prefixWord ++ tailWord_473169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473173 : List Nat := [1, 3, 2, 2, 1, 5, 1, 1, 1, 6]
def baseStart_473173 : Nat := 118140960795 + 473173 * 2 ^ 59
def prefixEnd_473173 : Nat := 4983230072969 + 3 ^ 40 * 473173 * 2
def baseEnd_473173 : Nat := 80988393909994147387141

theorem tailTrace_473173 : CollatzResearch.WordTrace tailWord_473173 prefixEnd_473173 80988393909994147387141 := by
  unfold tailWord_473173
  simp only [CollatzResearch.WordTrace]
  refine ⟨17258037114782507359776173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11505358076521671573184115 17258037114782507359776173)
  ·
    refine ⟨6471763918043440259916065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17258037114782507359776173 6471763918043440259916065)
    ·
      refine ⟨4853822938532580194937049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6471763918043440259916065 4853822938532580194937049)
      ·
        refine ⟨3640367203899435146202787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4853822938532580194937049 3640367203899435146202787)
        ·
          refine ⟨5460550805849152719304181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3640367203899435146202787 5460550805849152719304181)
          ·
            refine ⟨511926638048358067434767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5460550805849152719304181 511926638048358067434767)
            ·
              refine ⟨767889957072537101152151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511926638048358067434767 767889957072537101152151)
              ·
                refine ⟨1151834935608805651728227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767889957072537101152151 1151834935608805651728227)
                ·
                  refine ⟨1727752403413208477592341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1151834935608805651728227 1727752403413208477592341)
                  ·
                    refine ⟨80988393909994147387141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1727752403413208477592341 80988393909994147387141)
                    ·
                      rfl

theorem cell23_473173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_473173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473173 prefixEnd_473173 := by exact prefixLift 473173
  have htrace : WordTrace (prefixWord ++ tailWord_473173) baseStart_473173 baseEnd_473173 := by
    simpa [prefixWord, tailWord_473173, baseEnd_473173] using wordTrace_append hprefix tailTrace_473173
  have hstable : (prefixWord ++ tailWord_473173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473173).length < 2 ^ (prefixWord ++ tailWord_473173).sum := by decide
  have hdescent : baseEnd_473173 < baseStart_473173 := by decide
  rcases family_descends (prefixWord ++ tailWord_473173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473176 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 1, 1, 6]
def baseStart_473176 : Nat := 118140960795 + 473176 * 2 ^ 59
def prefixEnd_473176 : Nat := 4983230072969 + 3 ^ 40 * 473176 * 2
def baseEnd_473176 : Nat := 242966722171945930423909

theorem tailTrace_473176 : CollatzResearch.WordTrace tailWord_473176 prefixEnd_473176 242966722171945930423909 := by
  unfold tailWord_473176
  simp only [CollatzResearch.WordTrace]
  refine ⟨8629073266885819436067691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11505431022514425914756921 8629073266885819436067691)
  ·
    refine ⟨12943609900328729154101537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8629073266885819436067691 12943609900328729154101537)
    ·
      refine ⟨9707707425246546865576153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12943609900328729154101537 9707707425246546865576153)
      ·
        refine ⟨7280780568934910149182115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9707707425246546865576153 7280780568934910149182115)
        ·
          refine ⟨10921170853402365223773173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7280780568934910149182115 10921170853402365223773173)
          ·
            refine ⟨1023859767506471739728735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10921170853402365223773173 1023859767506471739728735)
            ·
              refine ⟨1535789651259707609593103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023859767506471739728735 1535789651259707609593103)
              ·
                refine ⟨2303684476889561414389655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535789651259707609593103 2303684476889561414389655)
                ·
                  refine ⟨3455526715334342121584483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2303684476889561414389655 3455526715334342121584483)
                  ·
                    refine ⟨5183290073001513182376725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3455526715334342121584483 5183290073001513182376725)
                    ·
                      refine ⟨242966722171945930423909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5183290073001513182376725 242966722171945930423909)
                      ·
                        rfl

theorem cell23_473176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_473176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473176 prefixEnd_473176 := by exact prefixLift 473176
  have htrace : WordTrace (prefixWord ++ tailWord_473176) baseStart_473176 baseEnd_473176 := by
    simpa [prefixWord, tailWord_473176, baseEnd_473176] using wordTrace_append hprefix tailTrace_473176
  have hstable : (prefixWord ++ tailWord_473176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473176).length < 2 ^ (prefixWord ++ tailWord_473176).sum := by decide
  have hdescent : baseEnd_473176 < baseStart_473176 := by decide
  rcases family_descends (prefixWord ++ tailWord_473176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473180 : List Nat := [2, 2, 4, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_473180 : Nat := 118140960795 + 473180 * 2 ^ 59
def prefixEnd_473180 : Nat := 4983230072969 + 3 ^ 40 * 473180 * 2
def baseEnd_473180 : Nat := 242968776094563914773891

theorem tailTrace_473180 : CollatzResearch.WordTrace tailWord_473180 prefixEnd_473180 242968776094563914773891 := by
  unfold tailWord_473180
  simp only [CollatzResearch.WordTrace]
  refine ⟨8629146212878573777640497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11505528283838098370187329 8629146212878573777640497)
  ·
    refine ⟨6471859659658930333230373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8629146212878573777640497 6471859659658930333230373)
    ·
      refine ⟨1213473686186049437480695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6471859659658930333230373 1213473686186049437480695)
      ·
        refine ⟨1820210529279074156221043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1213473686186049437480695 1820210529279074156221043)
        ·
          refine ⟨2730315793918611234331565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820210529279074156221043 2730315793918611234331565)
          ·
            refine ⟨1023868422719479212874337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2730315793918611234331565 1023868422719479212874337)
            ·
              refine ⟨767901317039609409655753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1023868422719479212874337 767901317039609409655753)
              ·
                refine ⟨575925987779707057241815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767901317039609409655753 575925987779707057241815)
                ·
                  refine ⟨863888981669560585862723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575925987779707057241815 863888981669560585862723)
                  ·
                    refine ⟨1295833472504340878794085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 863888981669560585862723 1295833472504340878794085)
                    ·
                      refine ⟨242968776094563914773891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1295833472504340878794085 242968776094563914773891)
                      ·
                        rfl

theorem cell23_473180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_473180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473180 prefixEnd_473180 := by exact prefixLift 473180
  have htrace : WordTrace (prefixWord ++ tailWord_473180) baseStart_473180 baseEnd_473180 := by
    simpa [prefixWord, tailWord_473180, baseEnd_473180] using wordTrace_append hprefix tailTrace_473180
  have hstable : (prefixWord ++ tailWord_473180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473180).length < 2 ^ (prefixWord ++ tailWord_473180).sum := by decide
  have hdescent : baseEnd_473180 < baseStart_473180 := by decide
  rcases family_descends (prefixWord ++ tailWord_473180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473308 : List Nat := [2, 2, 5, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_473308 : Nat := 118140960795 + 473308 * 2 ^ 59
def prefixEnd_473308 : Nat := 4983230072969 + 3 ^ 40 * 473308 * 2
def baseEnd_473308 : Nat := 243034501618339413973303

theorem tailTrace_473308 : CollatzResearch.WordTrace tailWord_473308 prefixEnd_473308 243034501618339413973303 := by
  unfold tailWord_473308
  simp only [CollatzResearch.WordTrace]
  refine ⟨8631480484646712707970289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11508640646195616943960385 8631480484646712707970289)
  ·
    refine ⟨6473610363485034530977717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8631480484646712707970289 6473610363485034530977717)
    ·
      refine ⟨606900971576721987279161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6473610363485034530977717 606900971576721987279161)
      ·
        refine ⟨455175728682541490459371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 606900971576721987279161 455175728682541490459371)
        ·
          refine ⟨682763593023812235689057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455175728682541490459371 682763593023812235689057)
          ·
            refine ⟨512072694767859176766793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682763593023812235689057 512072694767859176766793)
            ·
              refine ⟨384054521075894382575095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512072694767859176766793 384054521075894382575095)
              ·
                refine ⟨576081781613841573862643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384054521075894382575095 576081781613841573862643)
                ·
                  refine ⟨864122672420762360793965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 576081781613841573862643 864122672420762360793965)
                  ·
                    refine ⟨324046002157785885297737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 864122672420762360793965 324046002157785885297737)
                    ·
                      refine ⟨243034501618339413973303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 324046002157785885297737 243034501618339413973303)
                      ·
                        rfl

theorem cell23_473308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_473308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473308 prefixEnd_473308 := by exact prefixLift 473308
  have htrace : WordTrace (prefixWord ++ tailWord_473308) baseStart_473308 baseEnd_473308 := by
    simpa [prefixWord, tailWord_473308, baseEnd_473308] using wordTrace_append hprefix tailTrace_473308
  have hstable : (prefixWord ++ tailWord_473308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473308).length < 2 ^ (prefixWord ++ tailWord_473308).sum := by decide
  have hdescent : baseEnd_473308 < baseStart_473308 := by decide
  rcases family_descends (prefixWord ++ tailWord_473308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473363 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 3]
def baseStart_473363 : Nat := 118140960795 + 473363 * 2 ^ 59
def prefixEnd_473363 : Nat := 4983230072969 + 3 ^ 40 * 473363 * 2
def baseEnd_473363 : Nat := 243062743054336698785549

theorem tailTrace_473363 : CollatzResearch.WordTrace tailWord_473363 prefixEnd_473363 243062743054336698785549 := by
  unfold tailWord_473363
  simp only [CollatzResearch.WordTrace]
  refine ⟨17264966984094169809192743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11509977989396113206128495 17264966984094169809192743)
  ·
    refine ⟨25897450476141254713789115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17264966984094169809192743 25897450476141254713789115)
    ·
      refine ⟨38846175714211882070683673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25897450476141254713789115 38846175714211882070683673)
      ·
        refine ⟨29134631785658911553012755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38846175714211882070683673 29134631785658911553012755)
        ·
          refine ⟨43701947678488367329519133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29134631785658911553012755 43701947678488367329519133)
          ·
            refine ⟨16388230379433137748569675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43701947678488367329519133 16388230379433137748569675)
            ·
              refine ⟨24582345569149706622854513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16388230379433137748569675 24582345569149706622854513)
              ·
                refine ⟨18436759176862279967140885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24582345569149706622854513 18436759176862279967140885)
                ·
                  refine ⟨864223086415419373459729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18436759176862279967140885 864223086415419373459729)
                  ·
                    refine ⟨648167314811564530094797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 864223086415419373459729 648167314811564530094797)
                    ·
                      refine ⟨243062743054336698785549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 648167314811564530094797 243062743054336698785549)
                      ·
                        rfl

theorem cell23_473363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 3].length) (baseStart_473363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473363 prefixEnd_473363 := by exact prefixLift 473363
  have htrace : WordTrace (prefixWord ++ tailWord_473363) baseStart_473363 baseEnd_473363 := by
    simpa [prefixWord, tailWord_473363, baseEnd_473363] using wordTrace_append hprefix tailTrace_473363
  have hstable : (prefixWord ++ tailWord_473363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473363).length < 2 ^ (prefixWord ++ tailWord_473363).sum := by decide
  have hdescent : baseEnd_473363 < baseStart_473363 := by decide
  rcases family_descends (prefixWord ++ tailWord_473363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473380 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 4, 2, 3]
def baseStart_473380 : Nat := 118140960795 + 473380 * 2 ^ 59
def prefixEnd_473380 : Nat := 4983230072969 + 3 ^ 40 * 473380 * 2
def baseEnd_473380 : Nat := 243071472225463132272971

theorem tailTrace_473380 : CollatzResearch.WordTrace tailWord_473380 prefixEnd_473380 243071472225463132272971 := by
  unfold tailWord_473380
  simp only [CollatzResearch.WordTrace]
  refine ⟨8632793512516290856280797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11510391350021721141707729 8632793512516290856280797)
  ·
    refine ⟨3237297567193609071105299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8632793512516290856280797 3237297567193609071105299)
    ·
      refine ⟨4855946350790413606657949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3237297567193609071105299 4855946350790413606657949)
      ·
        refine ⟨1820979881546405102496731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4855946350790413606657949 1820979881546405102496731)
        ·
          refine ⟨2731469822319607653745097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820979881546405102496731 2731469822319607653745097)
          ·
            refine ⟨2048602366739705740308823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2731469822319607653745097 2048602366739705740308823)
            ·
              refine ⟨3072903550109558610463235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048602366739705740308823 3072903550109558610463235)
              ·
                refine ⟨4609355325164337915694853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3072903550109558610463235 4609355325164337915694853)
                ·
                  refine ⟨864254123468313359192785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4609355325164337915694853 864254123468313359192785)
                  ·
                    refine ⟨648190592601235019394589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 864254123468313359192785 648190592601235019394589)
                    ·
                      refine ⟨243071472225463132272971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 648190592601235019394589 243071472225463132272971)
                      ·
                        rfl

theorem cell23_473380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_473380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473380 prefixEnd_473380 := by exact prefixLift 473380
  have htrace : WordTrace (prefixWord ++ tailWord_473380) baseStart_473380 baseEnd_473380 := by
    simpa [prefixWord, tailWord_473380, baseEnd_473380] using wordTrace_append hprefix tailTrace_473380
  have hstable : (prefixWord ++ tailWord_473380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473380).length < 2 ^ (prefixWord ++ tailWord_473380).sum := by decide
  have hdescent : baseEnd_473380 < baseStart_473380 := by decide
  rcases family_descends (prefixWord ++ tailWord_473380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473400 : List Nat := [2, 1, 2, 1, 3, 1, 6, 1, 6]
def baseStart_473400 : Nat := 118140960795 + 473400 * 2 ^ 59
def prefixEnd_473400 : Nat := 4983230072969 + 3 ^ 40 * 473400 * 2
def baseEnd_473400 : Nat := 27009082426505894891431

theorem tailTrace_473400 : CollatzResearch.WordTrace tailWord_473400 prefixEnd_473400 27009082426505894891431 := by
  unfold tailWord_473400
  simp only [CollatzResearch.WordTrace]
  refine ⟨8633158242480062564144827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11510877656640083418859769 8633158242480062564144827)
  ·
    refine ⟨12949737363720093846217241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8633158242480062564144827 12949737363720093846217241)
    ·
      refine ⟨9712303022790070384662931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12949737363720093846217241 9712303022790070384662931)
      ·
        refine ⟨14568454534185105576994397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9712303022790070384662931 14568454534185105576994397)
        ·
          refine ⟨5463170450319414591372899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14568454534185105576994397 5463170450319414591372899)
          ·
            refine ⟨8194755675479121887059349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5463170450319414591372899 8194755675479121887059349)
            ·
              refine ⟨384129172288083838455907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8194755675479121887059349 384129172288083838455907)
              ·
                refine ⟨576193758432125757683861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384129172288083838455907 576193758432125757683861)
                ·
                  refine ⟨27009082426505894891431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 576193758432125757683861 27009082426505894891431)
                  ·
                    rfl

theorem cell23_473400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 6].length) (baseStart_473400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473400 prefixEnd_473400 := by exact prefixLift 473400
  have htrace : WordTrace (prefixWord ++ tailWord_473400) baseStart_473400 baseEnd_473400 := by
    simpa [prefixWord, tailWord_473400, baseEnd_473400] using wordTrace_append hprefix tailTrace_473400
  have hstable : (prefixWord ++ tailWord_473400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473400).length < 2 ^ (prefixWord ++ tailWord_473400).sum := by decide
  have hdescent : baseEnd_473400 < baseStart_473400 := by decide
  rcases family_descends (prefixWord ++ tailWord_473400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473443 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 3, 6]
def baseStart_473443 : Nat := 118140960795 + 473443 * 2 ^ 59
def prefixEnd_473443 : Nat := 4983230072969 + 3 ^ 40 * 473443 * 2
def baseEnd_473443 : Nat := 81034607168898795261727

theorem tailTrace_473443 : CollatzResearch.WordTrace tailWord_473443 prefixEnd_473443 81034607168898795261727 := by
  unfold tailWord_473443
  simp only [CollatzResearch.WordTrace]
  refine ⟨17267884823804343472104983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11511923215869562314736655 17267884823804343472104983)
  ·
    refine ⟨25901827235706515208157475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17267884823804343472104983 25901827235706515208157475)
    ·
      refine ⟨38852740853559772812236213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25901827235706515208157475 38852740853559772812236213)
      ·
        refine ⟨3642444455021228701147145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38852740853559772812236213 3642444455021228701147145)
        ·
          refine ⟨2731833341265921525860359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3642444455021228701147145 2731833341265921525860359)
          ·
            refine ⟨4097750011898882288790539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2731833341265921525860359 4097750011898882288790539)
            ·
              refine ⟨6146625017848323433185809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4097750011898882288790539 6146625017848323433185809)
              ·
                refine ⟨4609968763386242574889357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6146625017848323433185809 4609968763386242574889357)
                ·
                  refine ⟨1728738286269840965583509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4609968763386242574889357 1728738286269840965583509)
                  ·
                    refine ⟨81034607168898795261727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1728738286269840965583509 81034607168898795261727)
                    ·
                      rfl

theorem cell23_473443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 6].length) (baseStart_473443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473443 prefixEnd_473443 := by exact prefixLift 473443
  have htrace : WordTrace (prefixWord ++ tailWord_473443) baseStart_473443 baseEnd_473443 := by
    simpa [prefixWord, tailWord_473443, baseEnd_473443] using wordTrace_append hprefix tailTrace_473443
  have hstable : (prefixWord ++ tailWord_473443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473443).length < 2 ^ (prefixWord ++ tailWord_473443).sum := by decide
  have hdescent : baseEnd_473443 < baseStart_473443 := by decide
  rcases family_descends (prefixWord ++ tailWord_473443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473444 : List Nat := [2, 3, 1, 1, 3, 1, 3, 4, 1, 1, 3]
def baseStart_473444 : Nat := 118140960795 + 473444 * 2 ^ 59
def prefixEnd_473444 : Nat := 4983230072969 + 3 ^ 40 * 473444 * 2
def baseEnd_473444 : Nat := 243104334987350881872677

theorem tailTrace_473444 : CollatzResearch.WordTrace tailWord_473444 prefixEnd_473444 243104334987350881872677 := by
  unfold tailWord_473444
  simp only [CollatzResearch.WordTrace]
  refine ⟨8633960648400360321445693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11511947531200480428594257 8633960648400360321445693)
  ·
    refine ⟨3237735243150135120542135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8633960648400360321445693 3237735243150135120542135)
    ·
      refine ⟨4856602864725202680813203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3237735243150135120542135 4856602864725202680813203)
      ·
        refine ⟨7284904297087804021219805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4856602864725202680813203 7284904297087804021219805)
        ·
          refine ⟨2731839111407926507957427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7284904297087804021219805 2731839111407926507957427)
          ·
            refine ⟨4097758667111889761936141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2731839111407926507957427 4097758667111889761936141)
            ·
              refine ⟨1536659500166958660726053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4097758667111889761936141 1536659500166958660726053)
              ·
                refine ⟨288123656281304748886135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1536659500166958660726053 288123656281304748886135)
                ·
                  refine ⟨432185484421957123329203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288123656281304748886135 432185484421957123329203)
                  ·
                    refine ⟨648278226632935684993805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 432185484421957123329203 648278226632935684993805)
                    ·
                      refine ⟨243104334987350881872677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 648278226632935684993805 243104334987350881872677)
                      ·
                        rfl

theorem cell23_473444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 1, 1, 3].length) (baseStart_473444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473444 prefixEnd_473444 := by exact prefixLift 473444
  have htrace : WordTrace (prefixWord ++ tailWord_473444) baseStart_473444 baseEnd_473444 := by
    simpa [prefixWord, tailWord_473444, baseEnd_473444] using wordTrace_append hprefix tailTrace_473444
  have hstable : (prefixWord ++ tailWord_473444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473444).length < 2 ^ (prefixWord ++ tailWord_473444).sum := by decide
  have hdescent : baseEnd_473444 < baseStart_473444 := by decide
  rcases family_descends (prefixWord ++ tailWord_473444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473467 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 5, 2, 2]
def baseStart_473467 : Nat := 118140960795 + 473467 * 2 ^ 59
def prefixEnd_473467 : Nat := 4983230072969 + 3 ^ 40 * 473467 * 2
def baseEnd_473467 : Nat := 243116145042404291885071

theorem tailTrace_473467 : CollatzResearch.WordTrace tailWord_473467 prefixEnd_473467 243116145042404291885071 := by
  unfold tailWord_473467
  simp only [CollatzResearch.WordTrace]
  refine ⟨17268760175717395570978655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11512506783811597047319103 17268760175717395570978655)
  ·
    refine ⟨25903140263576093356467983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17268760175717395570978655 25903140263576093356467983)
    ·
      refine ⟨38854710395364140034701975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25903140263576093356467983 38854710395364140034701975)
      ·
        refine ⟨58282065593046210052052963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38854710395364140034701975 58282065593046210052052963)
        ·
          refine ⟨87423098389569315078079445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58282065593046210052052963 87423098389569315078079445)
          ·
            refine ⟨2048978868505530822142487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 87423098389569315078079445 2048978868505530822142487)
            ·
              refine ⟨3073468302758296233213731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048978868505530822142487 3073468302758296233213731)
              ·
                refine ⟨4610202454137444349820597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3073468302758296233213731 4610202454137444349820597)
                ·
                  refine ⟨432206480075385407795681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4610202454137444349820597 432206480075385407795681)
                  ·
                    refine ⟨324154860056539055846761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 432206480075385407795681 324154860056539055846761)
                    ·
                      refine ⟨243116145042404291885071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 324154860056539055846761 243116145042404291885071)
                      ·
                        rfl

theorem cell23_473467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 2, 2].length) (baseStart_473467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473467 prefixEnd_473467 := by exact prefixLift 473467
  have htrace : WordTrace (prefixWord ++ tailWord_473467) baseStart_473467 baseEnd_473467 := by
    simpa [prefixWord, tailWord_473467, baseEnd_473467] using wordTrace_append hprefix tailTrace_473467
  have hstable : (prefixWord ++ tailWord_473467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473467).length < 2 ^ (prefixWord ++ tailWord_473467).sum := by decide
  have hdescent : baseEnd_473467 < baseStart_473467 := by decide
  rcases family_descends (prefixWord ++ tailWord_473467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473480 : List Nat := [2, 1, 3, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_473480 : Nat := 118140960795 + 473480 * 2 ^ 59
def prefixEnd_473480 : Nat := 4983230072969 + 3 ^ 40 * 473480 * 2
def baseEnd_473480 : Nat := 243122820290912741022511

theorem tailTrace_473480 : CollatzResearch.WordTrace tailWord_473480 prefixEnd_473480 243122820290912741022511 := by
  unfold tailWord_473480
  simp only [CollatzResearch.WordTrace]
  refine ⟨8634617162335149395600947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11512822883113532527467929 8634617162335149395600947)
  ·
    refine ⟨12951925743502724093401421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8634617162335149395600947 12951925743502724093401421)
    ·
      refine ⟨4856972153813521535025533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12951925743502724093401421 4856972153813521535025533)
      ·
        refine ⟨1821364557680070575634575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4856972153813521535025533 1821364557680070575634575)
        ·
          refine ⟨2732046836520105863451863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1821364557680070575634575 2732046836520105863451863)
          ·
            refine ⟨4098070254780158795177795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2732046836520105863451863 4098070254780158795177795)
            ·
              refine ⟨6147105382170238192766693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4098070254780158795177795 6147105382170238192766693)
              ·
                refine ⟨1152582259156919661143755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6147105382170238192766693 1152582259156919661143755)
                ·
                  refine ⟨1728873388735379491715633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1152582259156919661143755 1728873388735379491715633)
                  ·
                    refine ⟨1296655041551534618786725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1728873388735379491715633 1296655041551534618786725)
                    ·
                      refine ⟨243122820290912741022511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1296655041551534618786725 243122820290912741022511)
                      ·
                        rfl

theorem cell23_473480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_473480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473480 prefixEnd_473480 := by exact prefixLift 473480
  have htrace : WordTrace (prefixWord ++ tailWord_473480) baseStart_473480 baseEnd_473480 := by
    simpa [prefixWord, tailWord_473480, baseEnd_473480] using wordTrace_append hprefix tailTrace_473480
  have hstable : (prefixWord ++ tailWord_473480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473480).length < 2 ^ (prefixWord ++ tailWord_473480).sum := by decide
  have hdescent : baseEnd_473480 < baseStart_473480 := by decide
  rcases family_descends (prefixWord ++ tailWord_473480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473484 : List Nat := [2, 2, 1, 2, 1, 6, 2, 1, 1, 1, 4]
def baseStart_473484 : Nat := 118140960795 + 473484 * 2 ^ 59
def prefixEnd_473484 : Nat := 4983230072969 + 3 ^ 40 * 473484 * 2
def baseEnd_473484 : Nat := 243124874213530725372493

theorem tailTrace_473484 : CollatzResearch.WordTrace tailWord_473484 prefixEnd_473484 243124874213530725372493 := by
  unfold tailWord_473484
  simp only [CollatzResearch.WordTrace]
  refine ⟨8634690108327903737173753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11512920144437204982898337 8634690108327903737173753)
  ·
    refine ⟨6476017581245927802880315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8634690108327903737173753 6476017581245927802880315)
    ·
      refine ⟨9714026371868891704320473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6476017581245927802880315 9714026371868891704320473)
      ·
        refine ⟨7285519778901668778240355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9714026371868891704320473 7285519778901668778240355)
        ·
          refine ⟨10928279668352503167360533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7285519778901668778240355 10928279668352503167360533)
          ·
            refine ⟨512263109454023585970025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10928279668352503167360533 512263109454023585970025)
            ·
              refine ⟨384197332090517689477519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512263109454023585970025 384197332090517689477519)
              ·
                refine ⟨576295998135776534216279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384197332090517689477519 576295998135776534216279)
                ·
                  refine ⟨864443997203664801324419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 576295998135776534216279 864443997203664801324419)
                  ·
                    refine ⟨1296665995805497201986629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 864443997203664801324419 1296665995805497201986629)
                    ·
                      refine ⟨243124874213530725372493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1296665995805497201986629 243124874213530725372493)
                      ·
                        rfl

theorem cell23_473484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_473484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473484 prefixEnd_473484 := by exact prefixLift 473484
  have htrace : WordTrace (prefixWord ++ tailWord_473484) baseStart_473484 baseEnd_473484 := by
    simpa [prefixWord, tailWord_473484, baseEnd_473484] using wordTrace_append hprefix tailTrace_473484
  have hstable : (prefixWord ++ tailWord_473484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473484).length < 2 ^ (prefixWord ++ tailWord_473484).sum := by decide
  have hdescent : baseEnd_473484 < baseStart_473484 := by decide
  rcases family_descends (prefixWord ++ tailWord_473484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473493 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_473493 : Nat := 118140960795 + 473493 * 2 ^ 59
def prefixEnd_473493 : Nat := 4983230072969 + 3 ^ 40 * 473493 * 2
def baseEnd_473493 : Nat := 243129495539421190159951

theorem tailTrace_473493 : CollatzResearch.WordTrace tailWord_473493 prefixEnd_473493 243129495539421190159951 := by
  unfold tailWord_473493
  simp only [CollatzResearch.WordTrace]
  refine ⟨17269708473623202011425133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11513138982415468007616755 17269708473623202011425133)
  ·
    refine ⟨6476140677608700754284425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17269708473623202011425133 6476140677608700754284425)
    ·
      refine ⟨4857105508206525565713319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6476140677608700754284425 4857105508206525565713319)
      ·
        refine ⟨7285658262309788348569979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4857105508206525565713319 7285658262309788348569979)
        ·
          refine ⟨10928487393464682522854969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7285658262309788348569979 10928487393464682522854969)
          ·
            refine ⟨8196365545098511892141227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10928487393464682522854969 8196365545098511892141227)
            ·
              refine ⟨12294548317647767838211841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8196365545098511892141227 12294548317647767838211841)
              ·
                refine ⟨9220911238235825878658881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12294548317647767838211841 9220911238235825878658881)
                ·
                  refine ⟨6915683428676869408994161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9220911238235825878658881 6915683428676869408994161)
                  ·
                    refine ⟨5186762571507652056745621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6915683428676869408994161 5186762571507652056745621)
                    ·
                      refine ⟨243129495539421190159951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5186762571507652056745621 243129495539421190159951)
                      ·
                        rfl

theorem cell23_473493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_473493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473493 prefixEnd_473493 := by exact prefixLift 473493
  have htrace : WordTrace (prefixWord ++ tailWord_473493) baseStart_473493 baseEnd_473493 := by
    simpa [prefixWord, tailWord_473493, baseEnd_473493] using wordTrace_append hprefix tailTrace_473493
  have hstable : (prefixWord ++ tailWord_473493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473493).length < 2 ^ (prefixWord ++ tailWord_473493).sum := by decide
  have hdescent : baseEnd_473493 < baseStart_473493 := by decide
  rcases family_descends (prefixWord ++ tailWord_473493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473501 : List Nat := [1, 4, 2, 1, 4, 1, 2, 1, 3, 2, 2]
def baseStart_473501 : Nat := 118140960795 + 473501 * 2 ^ 59
def prefixEnd_473501 : Nat := 4983230072969 + 3 ^ 40 * 473501 * 2
def baseEnd_473501 : Nat := 243133603384657158859915

theorem tailTrace_473501 : CollatzResearch.WordTrace tailWord_473501 prefixEnd_473501 243133603384657158859915 := by
  unfold tailWord_473501
  simp only [CollatzResearch.WordTrace]
  refine ⟨17270000257594219377716357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11513333505062812918477571 17270000257594219377716357)
  ·
    refine ⟨3238125048298916133321817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17270000257594219377716357 3238125048298916133321817)
    ·
      refine ⟨2428593786224187099991363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3238125048298916133321817 2428593786224187099991363)
      ·
        refine ⟨3642890679336280649987045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2428593786224187099991363 3642890679336280649987045)
        ·
          refine ⟨683042002375552621872571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3642890679336280649987045 683042002375552621872571)
          ·
            refine ⟨1024563003563328932808857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683042002375552621872571 1024563003563328932808857)
            ·
              refine ⟨768422252672496699606643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1024563003563328932808857 768422252672496699606643)
              ·
                refine ⟨1152633379008745049409965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 768422252672496699606643 1152633379008745049409965)
                ·
                  refine ⟨432237517128279393528737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1152633379008745049409965 432237517128279393528737)
                  ·
                    refine ⟨324178137846209545146553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 432237517128279393528737 324178137846209545146553)
                    ·
                      refine ⟨243133603384657158859915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 324178137846209545146553 243133603384657158859915)
                      ·
                        rfl

theorem cell23_473501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_473501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473501 prefixEnd_473501 := by exact prefixLift 473501
  have htrace : WordTrace (prefixWord ++ tailWord_473501) baseStart_473501 baseEnd_473501 := by
    simpa [prefixWord, tailWord_473501, baseEnd_473501] using wordTrace_append hprefix tailTrace_473501
  have hstable : (prefixWord ++ tailWord_473501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473501).length < 2 ^ (prefixWord ++ tailWord_473501).sum := by decide
  have hdescent : baseEnd_473501 < baseStart_473501 := by decide
  rcases family_descends (prefixWord ++ tailWord_473501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473513 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 4, 2, 5]
def baseStart_473513 : Nat := 118140960795 + 473513 * 2 ^ 59
def prefixEnd_473513 : Nat := 4983230072969 + 3 ^ 40 * 473513 * 2
def baseEnd_473513 : Nat := 243139765152511111909859

theorem tailTrace_473513 : CollatzResearch.WordTrace tailWord_473513 prefixEnd_473513 243139765152511111909859 := by
  unfold tailWord_473513
  simp only [CollatzResearch.WordTrace]
  refine ⟨17270437933550745427153193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11513625289033830284768795 17270437933550745427153193)
  ·
    refine ⟨12952828450163059070364895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17270437933550745427153193 12952828450163059070364895)
    ·
      refine ⟨19429242675244588605547343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12952828450163059070364895 19429242675244588605547343)
      ·
        refine ⟨29143864012866882908321015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19429242675244588605547343 29143864012866882908321015)
        ·
          refine ⟨43715796019300324362481523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29143864012866882908321015 43715796019300324362481523)
          ·
            refine ⟨65573694028950486543722285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43715796019300324362481523 65573694028950486543722285)
            ·
              refine ⟨24590135260856432453895857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65573694028950486543722285 24590135260856432453895857)
              ·
                refine ⟨18442601445642324340421893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24590135260856432453895857 18442601445642324340421893)
                ·
                  refine ⟨3457987771057935813829105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18442601445642324340421893 3457987771057935813829105)
                  ·
                    refine ⟨2593490828293451860371829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3457987771057935813829105 2593490828293451860371829)
                    ·
                      refine ⟨243139765152511111909859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2593490828293451860371829 243139765152511111909859)
                      ·
                        rfl

theorem cell23_473513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_473513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473513 prefixEnd_473513 := by exact prefixLift 473513
  have htrace : WordTrace (prefixWord ++ tailWord_473513) baseStart_473513 baseEnd_473513 := by
    simpa [prefixWord, tailWord_473513, baseEnd_473513] using wordTrace_append hprefix tailTrace_473513
  have hstable : (prefixWord ++ tailWord_473513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473513).length < 2 ^ (prefixWord ++ tailWord_473513).sum := by decide
  have hdescent : baseEnd_473513 < baseStart_473513 := by decide
  rcases family_descends (prefixWord ++ tailWord_473513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473524 : List Nat := [2, 5, 2, 2, 1, 1, 1, 9]
def baseStart_473524 : Nat := 118140960795 + 473524 * 2 ^ 59
def prefixEnd_473524 : Nat := 4983230072969 + 3 ^ 40 * 473524 * 2
def baseEnd_473524 : Nat := 9005385682952243291567

theorem tailTrace_473524 : CollatzResearch.WordTrace tailWord_473524 prefixEnd_473524 9005385682952243291567 := by
  unfold tailWord_473524
  simp only [CollatzResearch.WordTrace]
  refine ⟨8635419568255447152901813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11513892757673929537202417 8635419568255447152901813)
  ·
    refine ⟨809570584523948170584545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8635419568255447152901813 809570584523948170584545)
    ·
      refine ⟨607177938392961127938409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 809570584523948170584545 607177938392961127938409)
      ·
        refine ⟨455383453794720845953807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 607177938392961127938409 455383453794720845953807)
        ·
          refine ⟨683075180692081268930711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455383453794720845953807 683075180692081268930711)
          ·
            refine ⟨1024612771038121903396067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683075180692081268930711 1024612771038121903396067)
            ·
              refine ⟨1536919156557182855094101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024612771038121903396067 1536919156557182855094101)
              ·
                refine ⟨9005385682952243291567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1536919156557182855094101 9005385682952243291567)
                ·
                  rfl

theorem cell23_473524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 9].length) (baseStart_473524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473524 prefixEnd_473524 := by exact prefixLift 473524
  have htrace : WordTrace (prefixWord ++ tailWord_473524) baseStart_473524 baseEnd_473524 := by
    simpa [prefixWord, tailWord_473524, baseEnd_473524] using wordTrace_append hprefix tailTrace_473524
  have hstable : (prefixWord ++ tailWord_473524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473524).length < 2 ^ (prefixWord ++ tailWord_473524).sum := by decide
  have hdescent : baseEnd_473524 < baseStart_473524 := by decide
  rcases family_descends (prefixWord ++ tailWord_473524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473544 : List Nat := [2, 1, 3, 1, 3, 2, 2, 3, 1, 3, 2]
def baseStart_473544 : Nat := 118140960795 + 473544 * 2 ^ 59
def prefixEnd_473544 : Nat := 4983230072969 + 3 ^ 40 * 473544 * 2
def baseEnd_473544 : Nat := 243155683052800490622217

theorem tailTrace_473544 : CollatzResearch.WordTrace tailWord_473544 prefixEnd_473544 243155683052800490622217 := by
  unfold tailWord_473544
  simp only [CollatzResearch.WordTrace]
  refine ⟨8635784298219218860765843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11514379064292291814354457 8635784298219218860765843)
  ·
    refine ⟨12953676447328828291148765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8635784298219218860765843 12953676447328828291148765)
    ·
      refine ⟨4857628667748310609180787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12953676447328828291148765 4857628667748310609180787)
      ·
        refine ⟨7286443001622465913771181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4857628667748310609180787 7286443001622465913771181)
        ·
          refine ⟨2732416125608424717664193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7286443001622465913771181 2732416125608424717664193)
          ·
            refine ⟨2049312094206318538248145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2732416125608424717664193 2049312094206318538248145)
            ·
              refine ⟨1536984070654738903686109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2049312094206318538248145 1536984070654738903686109)
              ·
                refine ⟨576369026495527088882291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1536984070654738903686109 576369026495527088882291)
                ·
                  refine ⟨864553539743290633323437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 576369026495527088882291 864553539743290633323437)
                  ·
                    refine ⟨324207577403733987496289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 864553539743290633323437 324207577403733987496289)
                    ·
                      refine ⟨243155683052800490622217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 324207577403733987496289 243155683052800490622217)
                      ·
                        rfl

theorem cell23_473544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_473544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473544 prefixEnd_473544 := by exact prefixLift 473544
  have htrace : WordTrace (prefixWord ++ tailWord_473544) baseStart_473544 baseEnd_473544 := by
    simpa [prefixWord, tailWord_473544, baseEnd_473544] using wordTrace_append hprefix tailTrace_473544
  have hstable : (prefixWord ++ tailWord_473544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473544).length < 2 ^ (prefixWord ++ tailWord_473544).sum := by decide
  have hdescent : baseEnd_473544 < baseStart_473544 := by decide
  rcases family_descends (prefixWord ++ tailWord_473544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473560 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 2, 4, 3]
def baseStart_473560 : Nat := 118140960795 + 473560 * 2 ^ 59
def prefixEnd_473560 : Nat := 4983230072969 + 3 ^ 40 * 473560 * 2
def baseEnd_473560 : Nat := 243163898743272428022143

theorem tailTrace_473560 : CollatzResearch.WordTrace tailWord_473560 prefixEnd_473560 243163898743272428022143 := by
  unfold tailWord_473560
  simp only [CollatzResearch.WordTrace]
  refine ⟨8636076082190236227057067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11514768109586981636076089 8636076082190236227057067)
  ·
    refine ⟨12954114123285354340585601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8636076082190236227057067 12954114123285354340585601)
    ·
      refine ⟨9715585592464015755439201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12954114123285354340585601 9715585592464015755439201)
      ·
        refine ⟨7286689194348011816579401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9715585592464015755439201 7286689194348011816579401)
        ·
          refine ⟨5465016895761008862434551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7286689194348011816579401 5465016895761008862434551)
          ·
            refine ⟨8197525343641513293651827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5465016895761008862434551 8197525343641513293651827)
            ·
              refine ⟨12296288015462269940477741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8197525343641513293651827 12296288015462269940477741)
              ·
                refine ⟨4611108005798351227679153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12296288015462269940477741 4611108005798351227679153)
                ·
                  refine ⟨3458331004348763420759365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4611108005798351227679153 3458331004348763420759365)
                  ·
                    refine ⟨648437063315393141392381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3458331004348763420759365 648437063315393141392381)
                    ·
                      refine ⟨243163898743272428022143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 648437063315393141392381 243163898743272428022143)
                      ·
                        rfl

theorem cell23_473560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_473560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473560 prefixEnd_473560 := by exact prefixLift 473560
  have htrace : WordTrace (prefixWord ++ tailWord_473560) baseStart_473560 baseEnd_473560 := by
    simpa [prefixWord, tailWord_473560, baseEnd_473560] using wordTrace_append hprefix tailTrace_473560
  have hstable : (prefixWord ++ tailWord_473560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473560).length < 2 ^ (prefixWord ++ tailWord_473560).sum := by decide
  have hdescent : baseEnd_473560 < baseStart_473560 := by decide
  rcases family_descends (prefixWord ++ tailWord_473560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473597 : List Nat := [1, 4, 1, 1, 1, 3, 2, 5, 5]
def baseStart_473597 : Nat := 118140960795 + 473597 * 2 ^ 59
def prefixEnd_473597 : Nat := 4983230072969 + 3 ^ 40 * 473597 * 2
def baseEnd_473597 : Nat := 27020321947498753695497

theorem tailTrace_473597 : CollatzResearch.WordTrace tailWord_473597 prefixEnd_473597 27020321947498753695497 := by
  unfold tailWord_473597
  simp only [CollatzResearch.WordTrace]
  refine ⟨17273501665246427773211045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11515667776830951848807363 17273501665246427773211045)
  ·
    refine ⟨3238781562233705207477071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17273501665246427773211045 3238781562233705207477071)
    ·
      refine ⟨4858172343350557811215607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3238781562233705207477071 4858172343350557811215607)
      ·
        refine ⟨7287258515025836716823411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4858172343350557811215607 7287258515025836716823411)
        ·
          refine ⟨10930887772538755075235117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7287258515025836716823411 10930887772538755075235117)
          ·
            refine ⟨4099082914702033153213169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10930887772538755075235117 4099082914702033153213169)
            ·
              refine ⟨3074312186026524864909877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4099082914702033153213169 3074312186026524864909877)
              ·
                refine ⟨288216767439986706085301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3074312186026524864909877 288216767439986706085301)
                ·
                  refine ⟨27020321947498753695497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 288216767439986706085301 27020321947498753695497)
                  ·
                    rfl

theorem cell23_473597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_473597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473597 prefixEnd_473597 := by exact prefixLift 473597
  have htrace : WordTrace (prefixWord ++ tailWord_473597) baseStart_473597 baseEnd_473597 := by
    simpa [prefixWord, tailWord_473597, baseEnd_473597] using wordTrace_append hprefix tailTrace_473597
  have hstable : (prefixWord ++ tailWord_473597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473597).length < 2 ^ (prefixWord ++ tailWord_473597).sum := by decide
  have hdescent : baseEnd_473597 < baseStart_473597 := by decide
  rcases family_descends (prefixWord ++ tailWord_473597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473614 : List Nat := [4, 1, 1, 2, 3, 2, 1, 4, 5]
def baseStart_473614 : Nat := 118140960795 + 473614 * 2 ^ 59
def prefixEnd_473614 : Nat := 4983230072969 + 3 ^ 40 * 473614 * 2
def baseEnd_473614 : Nat := 27021291855401690749655

theorem tailTrace_473614 : CollatzResearch.WordTrace tailWord_473614 prefixEnd_473614 27021291855401690749655 := by
  unfold tailWord_473614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2159265213273104959572487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11516081137456559784386597 2159265213273104959572487)
  ·
    refine ⟨3238897819909657439358731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2159265213273104959572487 3238897819909657439358731)
    ·
      refine ⟨4858346729864486159038097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3238897819909657439358731 4858346729864486159038097)
      ·
        refine ⟨3643760047398364619278573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4858346729864486159038097 3643760047398364619278573)
        ·
          refine ⟨1366410017774386732229465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3643760047398364619278573 1366410017774386732229465)
          ·
            refine ⟨1024807513330790049172099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1366410017774386732229465 1024807513330790049172099)
            ·
              refine ⟨1537211269996185073758149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024807513330790049172099 1537211269996185073758149)
              ·
                refine ⟨288227113124284701329653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1537211269996185073758149 288227113124284701329653)
                ·
                  refine ⟨27021291855401690749655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 288227113124284701329653 27021291855401690749655)
                  ·
                    rfl

theorem cell23_473614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_473614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473614 prefixEnd_473614 := by exact prefixLift 473614
  have htrace : WordTrace (prefixWord ++ tailWord_473614) baseStart_473614 baseEnd_473614 := by
    simpa [prefixWord, tailWord_473614, baseEnd_473614] using wordTrace_append hprefix tailTrace_473614
  have hstable : (prefixWord ++ tailWord_473614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473614).length < 2 ^ (prefixWord ++ tailWord_473614).sum := by decide
  have hdescent : baseEnd_473614 < baseStart_473614 := by decide
  rcases family_descends (prefixWord ++ tailWord_473614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473657 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 5, 4]
def baseStart_473657 : Nat := 118140960795 + 473657 * 2 ^ 59
def prefixEnd_473657 : Nat := 4983230072969 + 3 ^ 40 * 473657 * 2
def baseEnd_473657 : Nat := 81071235455586182836399

theorem tailTrace_473657 : CollatzResearch.WordTrace tailWord_473657 prefixEnd_473657 81071235455586182836399 := by
  unfold tailWord_473657
  simp only [CollatzResearch.WordTrace]
  refine ⟨17275690045029058020395225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11517126696686038680263483 17275690045029058020395225)
  ·
    refine ⟨12956767533771793515296419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17275690045029058020395225 12956767533771793515296419)
    ·
      refine ⟨19435151300657690272944629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12956767533771793515296419 19435151300657690272944629)
      ·
        refine ⟨1822045434436658463088559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19435151300657690272944629 1822045434436658463088559)
        ·
          refine ⟨2733068151654987694632839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1822045434436658463088559 2733068151654987694632839)
          ·
            refine ⟨4099602227482481541949259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733068151654987694632839 4099602227482481541949259)
            ·
              refine ⟨6149403341223722312923889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4099602227482481541949259 6149403341223722312923889)
              ·
                refine ⟨4612052505917791734692917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6149403341223722312923889 4612052505917791734692917)
                ·
                  refine ⟨432379922429792975127461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4612052505917791734692917 432379922429792975127461)
                  ·
                    refine ⟨81071235455586182836399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 432379922429792975127461 81071235455586182836399)
                    ·
                      rfl

theorem cell23_473657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 4].length) (baseStart_473657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473657 prefixEnd_473657 := by exact prefixLift 473657
  have htrace : WordTrace (prefixWord ++ tailWord_473657) baseStart_473657 baseEnd_473657 := by
    simpa [prefixWord, tailWord_473657, baseEnd_473657] using wordTrace_append hprefix tailTrace_473657
  have hstable : (prefixWord ++ tailWord_473657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473657).length < 2 ^ (prefixWord ++ tailWord_473657).sum := by decide
  have hdescent : baseEnd_473657 < baseStart_473657 := by decide
  rcases family_descends (prefixWord ++ tailWord_473657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473667 : List Nat := [1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 3]
def baseStart_473667 : Nat := 118140960795 + 473667 * 2 ^ 59
def prefixEnd_473667 : Nat := 4983230072969 + 3 ^ 40 * 473667 * 2
def baseEnd_473667 : Nat := 243218841173303509384151

theorem tailTrace_473667 : CollatzResearch.WordTrace tailWord_473667 prefixEnd_473667 243218841173303509384151 := by
  unfold tailWord_473667
  simp only [CollatzResearch.WordTrace]
  refine ⟨17276054774992829728259255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11517369849995219818839503 17276054774992829728259255)
  ·
    refine ⟨25914082162489244592388883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17276054774992829728259255 25914082162489244592388883)
    ·
      refine ⟨38871123243733866888583325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25914082162489244592388883 38871123243733866888583325)
      ·
        refine ⟨14576671216400200083218747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38871123243733866888583325 14576671216400200083218747)
        ·
          refine ⟨21865006824600300124828121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14576671216400200083218747 21865006824600300124828121)
          ·
            refine ⟨16398755118450225093621091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21865006824600300124828121 16398755118450225093621091)
            ·
              refine ⟨24598132677675337640431637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16398755118450225093621091 24598132677675337640431637)
              ·
                refine ⟨1153037469266031451895233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24598132677675337640431637 1153037469266031451895233)
                ·
                  refine ⟨864778101949523588921425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1153037469266031451895233 864778101949523588921425)
                  ·
                    refine ⟨648583576462142691691069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 864778101949523588921425 648583576462142691691069)
                    ·
                      refine ⟨243218841173303509384151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 648583576462142691691069 243218841173303509384151)
                      ·
                        rfl

theorem cell23_473667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_473667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473667 prefixEnd_473667 := by exact prefixLift 473667
  have htrace : WordTrace (prefixWord ++ tailWord_473667) baseStart_473667 baseEnd_473667 := by
    simpa [prefixWord, tailWord_473667, baseEnd_473667] using wordTrace_append hprefix tailTrace_473667
  have hstable : (prefixWord ++ tailWord_473667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473667).length < 2 ^ (prefixWord ++ tailWord_473667).sum := by decide
  have hdescent : baseEnd_473667 < baseStart_473667 := by decide
  rcases family_descends (prefixWord ++ tailWord_473667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473674 : List Nat := [3, 1, 2, 1, 1, 5, 2, 1, 3, 4]
def baseStart_473674 : Nat := 118140960795 + 473674 * 2 ^ 59
def prefixEnd_473674 : Nat := 4983230072969 + 3 ^ 40 * 473674 * 2
def baseEnd_473674 : Nat := 81074145179294993998873

theorem tailTrace_473674 : CollatzResearch.WordTrace tailWord_473674 prefixEnd_473674 81074145179294993998873 := by
  unfold tailWord_473674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4319077521491867480941019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11517540057311646615842717 4319077521491867480941019)
  ·
    refine ⟨6478616282237801221411529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4319077521491867480941019 6478616282237801221411529)
    ·
      refine ⟨4858962211678350916058647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6478616282237801221411529 4858962211678350916058647)
      ·
        refine ⟨7288443317517526374087971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4858962211678350916058647 7288443317517526374087971)
        ·
          refine ⟨10932664976276289561131957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7288443317517526374087971 10932664976276289561131957)
          ·
            refine ⟨1024937341525902146356121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10932664976276289561131957 1024937341525902146356121)
            ·
              refine ⟨768703006144426609767091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1024937341525902146356121 768703006144426609767091)
              ·
                refine ⟨1153054509216639914650637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 768703006144426609767091 1153054509216639914650637)
                ·
                  refine ⟨432395440956239967993989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1153054509216639914650637 432395440956239967993989)
                  ·
                    refine ⟨81074145179294993998873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 432395440956239967993989 81074145179294993998873)
                    ·
                      rfl

theorem cell23_473674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_473674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473674 prefixEnd_473674 := by exact prefixLift 473674
  have htrace : WordTrace (prefixWord ++ tailWord_473674) baseStart_473674 baseEnd_473674 := by
    simpa [prefixWord, tailWord_473674, baseEnd_473674] using wordTrace_append hprefix tailTrace_473674
  have hstable : (prefixWord ++ tailWord_473674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473674).length < 2 ^ (prefixWord ++ tailWord_473674).sum := by decide
  have hdescent : baseEnd_473674 < baseStart_473674 := by decide
  rcases family_descends (prefixWord ++ tailWord_473674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473724 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 4, 3, 2]
def baseStart_473724 : Nat := 118140960795 + 473724 * 2 ^ 59
def prefixEnd_473724 : Nat := 4983230072969 + 3 ^ 40 * 473724 * 2
def baseEnd_473724 : Nat := 243248109570609786371389

theorem tailTrace_473724 : CollatzResearch.WordTrace tailWord_473724 prefixEnd_473724 243248109570609786371389 := by
  unfold tailWord_473724
  simp only [CollatzResearch.WordTrace]
  refine ⟨8639066867893164231542113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11518755823857552308722817 8639066867893164231542113)
  ·
    refine ⟨6479300150919873173656585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8639066867893164231542113 6479300150919873173656585)
    ·
      refine ⟨4859475113189904880242439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6479300150919873173656585 4859475113189904880242439)
      ·
        refine ⟨7289212669784857320363659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4859475113189904880242439 7289212669784857320363659)
        ·
          refine ⟨10933819004677285980545489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7289212669784857320363659 10933819004677285980545489)
          ·
            refine ⟨8200364253507964485409117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10933819004677285980545489 8200364253507964485409117)
            ·
              refine ⟨3075136595065486682028419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8200364253507964485409117 3075136595065486682028419)
              ·
                refine ⟨4612704892598230023042629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3075136595065486682028419 4612704892598230023042629)
                ·
                  refine ⟨864882167362168129320493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4612704892598230023042629 864882167362168129320493)
                  ·
                    refine ⟨324330812760813048495185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 864882167362168129320493 324330812760813048495185)
                    ·
                      refine ⟨243248109570609786371389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 324330812760813048495185 243248109570609786371389)
                      ·
                        rfl

theorem cell23_473724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_473724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473724 prefixEnd_473724 := by exact prefixLift 473724
  have htrace : WordTrace (prefixWord ++ tailWord_473724) baseStart_473724 baseEnd_473724 := by
    simpa [prefixWord, tailWord_473724, baseEnd_473724] using wordTrace_append hprefix tailTrace_473724
  have hstable : (prefixWord ++ tailWord_473724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473724).length < 2 ^ (prefixWord ++ tailWord_473724).sum := by decide
  have hdescent : baseEnd_473724 < baseStart_473724 := by decide
  rcases family_descends (prefixWord ++ tailWord_473724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473731 : List Nat := [1, 1, 1, 3, 3, 1, 2, 6, 1, 1, 3]
def baseStart_473731 : Nat := 118140960795 + 473731 * 2 ^ 59
def prefixEnd_473731 : Nat := 4983230072969 + 3 ^ 40 * 473731 * 2
def baseEnd_473731 : Nat := 243251703935191258983857

theorem tailTrace_473731 : CollatzResearch.WordTrace tailWord_473731 prefixEnd_473731 243251703935191258983857 := by
  unfold tailWord_473731
  simp only [CollatzResearch.WordTrace]
  refine ⟨17278389046760968658589047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11518926031173979105726031 17278389046760968658589047)
  ·
    refine ⟨25917583570141452987883571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17278389046760968658589047 25917583570141452987883571)
    ·
      refine ⟨38876375355212179481825357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25917583570141452987883571 38876375355212179481825357)
      ·
        refine ⟨14578640758204567305684509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38876375355212179481825357 14578640758204567305684509)
        ·
          refine ⟨5466990284326712739631691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14578640758204567305684509 5466990284326712739631691)
          ·
            refine ⟨8200485426490069109447537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5466990284326712739631691 8200485426490069109447537)
            ·
              refine ⟨6150364069867551832085653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8200485426490069109447537 6150364069867551832085653)
              ·
                refine ⟨288298315775041492129015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6150364069867551832085653 288298315775041492129015)
                ·
                  refine ⟨432447473662562238193523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288298315775041492129015 432447473662562238193523)
                  ·
                    refine ⟨648671210493843357290285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 432447473662562238193523 648671210493843357290285)
                    ·
                      refine ⟨243251703935191258983857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 648671210493843357290285 243251703935191258983857)
                      ·
                        rfl

theorem cell23_473731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 1, 1, 3].length) (baseStart_473731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473731 prefixEnd_473731 := by exact prefixLift 473731
  have htrace : WordTrace (prefixWord ++ tailWord_473731) baseStart_473731 baseEnd_473731 := by
    simpa [prefixWord, tailWord_473731, baseEnd_473731] using wordTrace_append hprefix tailTrace_473731
  have hstable : (prefixWord ++ tailWord_473731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473731).length < 2 ^ (prefixWord ++ tailWord_473731).sum := by decide
  have hdescent : baseEnd_473731 < baseStart_473731 := by decide
  rcases family_descends (prefixWord ++ tailWord_473731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473737 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 3, 1, 4]
def baseStart_473737 : Nat := 118140960795 + 473737 * 2 ^ 59
def prefixEnd_473737 : Nat := 4983230072969 + 3 ^ 40 * 473737 * 2
def baseEnd_473737 : Nat := 243254784819118235508829

theorem tailTrace_473737 : CollatzResearch.WordTrace tailWord_473737 prefixEnd_473737 243254784819118235508829 := by
  unfold tailWord_473737
  simp only [CollatzResearch.WordTrace]
  refine ⟨17278607884739231683307465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11519071923159487788871643 17278607884739231683307465)
  ·
    refine ⟨12958955913554423762480599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17278607884739231683307465 12958955913554423762480599)
    ·
      refine ⟨19438433870331635643720899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12958955913554423762480599 19438433870331635643720899)
      ·
        refine ⟨29157650805497453465581349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19438433870331635643720899 29157650805497453465581349)
        ·
          refine ⟨5467059526030772524796503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29157650805497453465581349 5467059526030772524796503)
          ·
            refine ⟨8200589289046158787194755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5467059526030772524796503 8200589289046158787194755)
            ·
              refine ⟨12300883933569238180792133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8200589289046158787194755 12300883933569238180792133)
              ·
                refine ⟨2306415737544232158898525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12300883933569238180792133 2306415737544232158898525)
                ·
                  refine ⟨864905901579087059586947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2306415737544232158898525 864905901579087059586947)
                  ·
                    refine ⟨1297358852368630589380421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 864905901579087059586947 1297358852368630589380421)
                    ·
                      refine ⟨243254784819118235508829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1297358852368630589380421 243254784819118235508829)
                      ·
                        rfl

theorem cell23_473737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 1, 4].length) (baseStart_473737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473737 prefixEnd_473737 := by exact prefixLift 473737
  have htrace : WordTrace (prefixWord ++ tailWord_473737) baseStart_473737 baseEnd_473737 := by
    simpa [prefixWord, tailWord_473737, baseEnd_473737] using wordTrace_append hprefix tailTrace_473737
  have hstable : (prefixWord ++ tailWord_473737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473737).length < 2 ^ (prefixWord ++ tailWord_473737).sum := by decide
  have hdescent : baseEnd_473737 < baseStart_473737 := by decide
  rcases family_descends (prefixWord ++ tailWord_473737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473738 : List Nat := [3, 1, 2, 3, 4, 1, 2, 1, 6]
def baseStart_473738 : Nat := 118140960795 + 473738 * 2 ^ 59
def prefixEnd_473738 : Nat := 4983230072969 + 3 ^ 40 * 473738 * 2
def baseEnd_473738 : Nat := 27028366477752525732925

theorem tailTrace_473738 : CollatzResearch.WordTrace tailWord_473738 prefixEnd_473738 27028366477752525732925 := by
  unfold tailWord_473738
  simp only [CollatzResearch.WordTrace]
  refine ⟨4319661089433902213523467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11519096238490405902729245 4319661089433902213523467)
  ·
    refine ⟨6479491634150853320285201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4319661089433902213523467 6479491634150853320285201)
    ·
      refine ⟨4859618725613139990213901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6479491634150853320285201 4859618725613139990213901)
      ·
        refine ⟨1822357022104927496330213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4859618725613139990213901 1822357022104927496330213)
        ·
          refine ⟨341691941644673905561915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1822357022104927496330213 341691941644673905561915)
          ·
            refine ⟨512537912467010858342873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341691941644673905561915 512537912467010858342873)
            ·
              refine ⟨384403434350258143757155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512537912467010858342873 384403434350258143757155)
              ·
                refine ⟨576605151525387215635733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384403434350258143757155 576605151525387215635733)
                ·
                  refine ⟨27028366477752525732925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 576605151525387215635733 27028366477752525732925)
                  ·
                    rfl

theorem cell23_473738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 6].length) (baseStart_473738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473738 prefixEnd_473738 := by exact prefixLift 473738
  have htrace : WordTrace (prefixWord ++ tailWord_473738) baseStart_473738 baseEnd_473738 := by
    simpa [prefixWord, tailWord_473738, baseEnd_473738] using wordTrace_append hprefix tailTrace_473738
  have hstable : (prefixWord ++ tailWord_473738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473738).length < 2 ^ (prefixWord ++ tailWord_473738).sum := by decide
  have hdescent : baseEnd_473738 < baseStart_473738 := by decide
  rcases family_descends (prefixWord ++ tailWord_473738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473757 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_473757 : Nat := 118140960795 + 473757 * 2 ^ 59
def prefixEnd_473757 : Nat := 4983230072969 + 3 ^ 40 * 473757 * 2
def baseEnd_473757 : Nat := 243265054432208157258737

theorem tailTrace_473757 : CollatzResearch.WordTrace tailWord_473757 prefixEnd_473757 243265054432208157258737 := by
  unfold tailWord_473757
  simp only [CollatzResearch.WordTrace]
  refine ⟨17279337344666775099035525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11519558229777850066023683 17279337344666775099035525)
  ·
    refine ⟨3239875752125020331069161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17279337344666775099035525 3239875752125020331069161)
    ·
      refine ⟨2429906814093765248301871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3239875752125020331069161 2429906814093765248301871)
      ·
        refine ⟨3644860221140647872452807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2429906814093765248301871 3644860221140647872452807)
        ·
          refine ⟨5467290331710971808679211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3644860221140647872452807 5467290331710971808679211)
          ·
            refine ⟨8200935497566457713018817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5467290331710971808679211 8200935497566457713018817)
            ·
              refine ⟨6150701623174843284764113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8200935497566457713018817 6150701623174843284764113)
              ·
                refine ⟨4613026217381132463573085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6150701623174843284764113 4613026217381132463573085)
                ·
                  refine ⟨1729884831517924673839907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4613026217381132463573085 1729884831517924673839907)
                  ·
                    refine ⟨2594827247276887010759861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1729884831517924673839907 2594827247276887010759861)
                    ·
                      refine ⟨243265054432208157258737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2594827247276887010759861 243265054432208157258737)
                      ·
                        rfl

theorem cell23_473757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_473757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473757 prefixEnd_473757 := by exact prefixLift 473757
  have htrace : WordTrace (prefixWord ++ tailWord_473757) baseStart_473757 baseEnd_473757 := by
    simpa [prefixWord, tailWord_473757, baseEnd_473757] using wordTrace_append hprefix tailTrace_473757
  have hstable : (prefixWord ++ tailWord_473757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473757).length < 2 ^ (prefixWord ++ tailWord_473757).sum := by decide
  have hdescent : baseEnd_473757 < baseStart_473757 := by decide
  rcases family_descends (prefixWord ++ tailWord_473757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473758 : List Nat := [4, 3, 1, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_473758 : Nat := 118140960795 + 473758 * 2 ^ 59
def prefixEnd_473758 : Nat := 4983230072969 + 3 ^ 40 * 473758 * 2
def baseEnd_473758 : Nat := 243265567912862653346233

theorem tailTrace_473758 : CollatzResearch.WordTrace tailWord_473758 prefixEnd_473758 243265567912862653346233 := by
  unfold tailWord_473758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2159921727207894033727741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11519582545108768179881285 2159921727207894033727741)
  ·
    refine ⟨809970647702960262647903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2159921727207894033727741 809970647702960262647903)
    ·
      refine ⟨1214955971554440393971855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 809970647702960262647903 1214955971554440393971855)
      ·
        refine ⟨1822433957331660590957783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1214955971554440393971855 1822433957331660590957783)
        ·
          refine ⟨2733650935997490886436675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1822433957331660590957783 2733650935997490886436675)
          ·
            refine ⟨4100476403996236329655013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733650935997490886436675 4100476403996236329655013)
            ·
              refine ⟨768839325749294311810315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4100476403996236329655013 768839325749294311810315)
              ·
                refine ⟨1153258988623941467715473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 768839325749294311810315 1153258988623941467715473)
                ·
                  refine ⟨864944241467956100786605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1153258988623941467715473 864944241467956100786605)
                  ·
                    refine ⟨324354090550483537794977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 864944241467956100786605 324354090550483537794977)
                    ·
                      refine ⟨243265567912862653346233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 324354090550483537794977 243265567912862653346233)
                      ·
                        rfl

theorem cell23_473758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_473758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473758 prefixEnd_473758 := by exact prefixLift 473758
  have htrace : WordTrace (prefixWord ++ tailWord_473758) baseStart_473758 baseEnd_473758 := by
    simpa [prefixWord, tailWord_473758, baseEnd_473758] using wordTrace_append hprefix tailTrace_473758
  have hstable : (prefixWord ++ tailWord_473758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473758).length < 2 ^ (prefixWord ++ tailWord_473758).sum := by decide
  have hdescent : baseEnd_473758 < baseStart_473758 := by decide
  rcases family_descends (prefixWord ++ tailWord_473758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473777 : List Nat := [1, 2, 2, 6, 12]
def baseStart_473777 : Nat := 118140960795 + 473777 * 2 ^ 59
def prefixEnd_473777 : Nat := 4983230072969 + 3 ^ 40 * 473777 * 2
def baseEnd_473777 : Nat := 333711006920847845005

theorem tailTrace_473777 : CollatzResearch.WordTrace tailWord_473777 prefixEnd_473777 333711006920847845005 := by
  unfold tailWord_473777
  simp only [CollatzResearch.WordTrace]
  refine ⟨17280066804594318514763585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11520044536396212343175723 17280066804594318514763585)
  ·
    refine ⟨12960050103445738886072689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17280066804594318514763585 12960050103445738886072689)
    ·
      refine ⟨9720037577584304164554517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12960050103445738886072689 9720037577584304164554517)
      ·
        refine ⟨455626761449264257713493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9720037577584304164554517 455626761449264257713493)
        ·
          refine ⟨333711006920847845005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 455626761449264257713493 333711006920847845005)
          ·
            rfl

theorem cell23_473777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 12].length) (baseStart_473777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473777 prefixEnd_473777 := by exact prefixLift 473777
  have htrace : WordTrace (prefixWord ++ tailWord_473777) baseStart_473777 baseEnd_473777 := by
    simpa [prefixWord, tailWord_473777, baseEnd_473777] using wordTrace_append hprefix tailTrace_473777
  have hstable : (prefixWord ++ tailWord_473777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473777).length < 2 ^ (prefixWord ++ tailWord_473777).sum := by decide
  have hdescent : baseEnd_473777 < baseStart_473777 := by decide
  rcases family_descends (prefixWord ++ tailWord_473777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473781 : List Nat := [1, 3, 3, 3, 1, 1, 1, 4, 2, 4]
def baseStart_473781 : Nat := 118140960795 + 473781 * 2 ^ 59
def prefixEnd_473781 : Nat := 4983230072969 + 3 ^ 40 * 473781 * 2
def baseEnd_473781 : Nat := 81092459322638687786209

theorem tailTrace_473781 : CollatzResearch.WordTrace tailWord_473781 prefixEnd_473781 81092459322638687786209 := by
  unfold tailWord_473781
  simp only [CollatzResearch.WordTrace]
  refine ⟨17280212696579827197909197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11520141797719884798606131 17280212696579827197909197)
  ·
    refine ⟨6480079761217435199215949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17280212696579827197909197 6480079761217435199215949)
    ·
      refine ⟨2430029910456538199705981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6480079761217435199215949 2430029910456538199705981)
      ·
        refine ⟨911261216421201824889743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2430029910456538199705981 911261216421201824889743)
        ·
          refine ⟨1366891824631802737334615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911261216421201824889743 1366891824631802737334615)
          ·
            refine ⟨2050337736947704106001923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1366891824631802737334615 2050337736947704106001923)
            ·
              refine ⟨3075506605421556159002885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2050337736947704106001923 3075506605421556159002885)
              ·
                refine ⟨576657488516541779813041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3075506605421556159002885 576657488516541779813041)
                ·
                  refine ⟨432493116387406334859781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576657488516541779813041 432493116387406334859781)
                  ·
                    refine ⟨81092459322638687786209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 432493116387406334859781 81092459322638687786209)
                    ·
                      rfl

theorem cell23_473781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_473781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473781 prefixEnd_473781 := by exact prefixLift 473781
  have htrace : WordTrace (prefixWord ++ tailWord_473781) baseStart_473781 baseEnd_473781 := by
    simpa [prefixWord, tailWord_473781, baseEnd_473781] using wordTrace_append hprefix tailTrace_473781
  have hstable : (prefixWord ++ tailWord_473781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473781).length < 2 ^ (prefixWord ++ tailWord_473781).sum := by decide
  have hdescent : baseEnd_473781 < baseStart_473781 := by decide
  rcases family_descends (prefixWord ++ tailWord_473781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473782 : List Nat := [5, 1, 3, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_473782 : Nat := 118140960795 + 473782 * 2 ^ 59
def prefixEnd_473782 : Nat := 4983230072969 + 3 ^ 40 * 473782 * 2
def baseEnd_473782 : Nat := 243277891448570559446123

theorem tailTrace_473782 : CollatzResearch.WordTrace tailWord_473782 prefixEnd_473782 243277891448570559446123 := by
  unfold tailWord_473782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1080015573098512773043475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11520166113050802912463733 1080015573098512773043475)
  ·
    refine ⟨1620023359647769159565213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1080015573098512773043475 1620023359647769159565213)
    ·
      refine ⟨607508759867913434836955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1620023359647769159565213 607508759867913434836955)
      ·
        refine ⟨911263139801870152255433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607508759867913434836955 911263139801870152255433)
        ·
          refine ⟨683447354851402614191575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 911263139801870152255433 683447354851402614191575)
          ·
            refine ⟨1025171032277103921287363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683447354851402614191575 1025171032277103921287363)
            ·
              refine ⟨1537756548415655881931045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025171032277103921287363 1537756548415655881931045)
              ·
                refine ⟨288329352827935477862071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1537756548415655881931045 288329352827935477862071)
                ·
                  refine ⟨432494029241903216793107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288329352827935477862071 432494029241903216793107)
                  ·
                    refine ⟨648741043862854825189661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 432494029241903216793107 648741043862854825189661)
                    ·
                      refine ⟨243277891448570559446123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 648741043862854825189661 243277891448570559446123)
                      ·
                        rfl

theorem cell23_473782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_473782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473782 prefixEnd_473782 := by exact prefixLift 473782
  have htrace : WordTrace (prefixWord ++ tailWord_473782) baseStart_473782 baseEnd_473782 := by
    simpa [prefixWord, tailWord_473782, baseEnd_473782] using wordTrace_append hprefix tailTrace_473782
  have hstable : (prefixWord ++ tailWord_473782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473782).length < 2 ^ (prefixWord ++ tailWord_473782).sum := by decide
  have hdescent : baseEnd_473782 < baseStart_473782 := by decide
  rcases family_descends (prefixWord ++ tailWord_473782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473817 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 2, 2, 5]
def baseStart_473817 : Nat := 118140960795 + 473817 * 2 ^ 59
def prefixEnd_473817 : Nat := 4983230072969 + 3 ^ 40 * 473817 * 2
def baseEnd_473817 : Nat := 243295863271477922508461

theorem tailTrace_473817 : CollatzResearch.WordTrace tailWord_473817 prefixEnd_473817 243295863271477922508461 := by
  unfold tailWord_473817
  simp only [CollatzResearch.WordTrace]
  refine ⟨17281525724449405346219705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11521017149632936897479803 17281525724449405346219705)
  ·
    refine ⟨12961144293337054009664779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17281525724449405346219705 12961144293337054009664779)
    ·
      refine ⟨19441716440005581014497169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12961144293337054009664779 19441716440005581014497169)
      ·
        refine ⟨14581287330004185760872877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19441716440005581014497169 14581287330004185760872877)
        ·
          refine ⟨5467982748751569660327329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14581287330004185760872877 5467982748751569660327329)
          ·
            refine ⟨4100987061563677245245497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5467982748751569660327329 4100987061563677245245497)
            ·
              refine ⟨3075740296172757933934123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4100987061563677245245497 3075740296172757933934123)
              ·
                refine ⟨4613610444259136900901185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3075740296172757933934123 4613610444259136900901185)
                ·
                  refine ⟨3460207833194352675675889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4613610444259136900901185 3460207833194352675675889)
                  ·
                    refine ⟨2595155874895764506756917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3460207833194352675675889 2595155874895764506756917)
                    ·
                      refine ⟨243295863271477922508461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2595155874895764506756917 243295863271477922508461)
                      ·
                        rfl

theorem cell23_473817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_473817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473817 prefixEnd_473817 := by exact prefixLift 473817
  have htrace : WordTrace (prefixWord ++ tailWord_473817) baseStart_473817 baseEnd_473817 := by
    simpa [prefixWord, tailWord_473817, baseEnd_473817] using wordTrace_append hprefix tailTrace_473817
  have hstable : (prefixWord ++ tailWord_473817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473817).length < 2 ^ (prefixWord ++ tailWord_473817).sum := by decide
  have hdescent : baseEnd_473817 < baseStart_473817 := by decide
  rcases family_descends (prefixWord ++ tailWord_473817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473838 : List Nat := [4, 1, 2, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_473838 : Nat := 118140960795 + 473838 * 2 ^ 59
def prefixEnd_473838 : Nat := 4983230072969 + 3 ^ 40 * 473838 * 2
def baseEnd_473838 : Nat := 243306646365222340345865

theorem tailTrace_473838 : CollatzResearch.WordTrace tailWord_473838 prefixEnd_473838 243306646365222340345865 := by
  unfold tailWord_473838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2160286457171665741591771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11521527771582217288489445 2160286457171665741591771)
  ·
    refine ⟨3240429685757498612387657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2160286457171665741591771 3240429685757498612387657)
    ·
      refine ⟨2430322264318123959290743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3240429685757498612387657 2430322264318123959290743)
      ·
        refine ⟨3645483396477185938936115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2430322264318123959290743 3645483396477185938936115)
        ·
          refine ⟨5468225094715778908404173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3645483396477185938936115 5468225094715778908404173)
          ·
            refine ⟨2050584410518417090651565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5468225094715778908404173 2050584410518417090651565)
            ·
              refine ⟨768969153944406408994337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2050584410518417090651565 768969153944406408994337)
              ·
                refine ⟨576726865458304806745753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 768969153944406408994337 576726865458304806745753)
                ·
                  refine ⟨432545149093728605059315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576726865458304806745753 432545149093728605059315)
                  ·
                    refine ⟨648817723640592907588973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 432545149093728605059315 648817723640592907588973)
                    ·
                      refine ⟨243306646365222340345865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 648817723640592907588973 243306646365222340345865)
                      ·
                        rfl

theorem cell23_473838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_473838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473838 prefixEnd_473838 := by exact prefixLift 473838
  have htrace : WordTrace (prefixWord ++ tailWord_473838) baseStart_473838 baseEnd_473838 := by
    simpa [prefixWord, tailWord_473838, baseEnd_473838] using wordTrace_append hprefix tailTrace_473838
  have hstable : (prefixWord ++ tailWord_473838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473838).length < 2 ^ (prefixWord ++ tailWord_473838).sum := by decide
  have hdescent : baseEnd_473838 < baseStart_473838 := by decide
  rcases family_descends (prefixWord ++ tailWord_473838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473847 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 5]
def baseStart_473847 : Nat := 118140960795 + 473847 * 2 ^ 59
def prefixEnd_473847 : Nat := 4983230072969 + 3 ^ 40 * 473847 * 2
def baseEnd_473847 : Nat := 243311267691112805133323

theorem tailTrace_473847 : CollatzResearch.WordTrace tailWord_473847 prefixEnd_473847 243311267691112805133323 := by
  unfold tailWord_473847
  simp only [CollatzResearch.WordTrace]
  refine ⟨17282619914340720469811795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11521746609560480313207863 17282619914340720469811795)
  ·
    refine ⟨25923929871511080704717693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17282619914340720469811795 25923929871511080704717693)
    ·
      refine ⟨9721473701816655264269135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25923929871511080704717693 9721473701816655264269135)
      ·
        refine ⟨14582210552724982896403703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9721473701816655264269135 14582210552724982896403703)
        ·
          refine ⟨21873315829087474344605555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14582210552724982896403703 21873315829087474344605555)
          ·
            refine ⟨32809973743631211516908333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21873315829087474344605555 32809973743631211516908333)
            ·
              refine ⟨12303740153861704318840625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32809973743631211516908333 12303740153861704318840625)
              ·
                refine ⟨9227805115396278239130469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12303740153861704318840625 9227805115396278239130469)
                ·
                  refine ⟨1730213459136802169836963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9227805115396278239130469 1730213459136802169836963)
                  ·
                    refine ⟨2595320188705203254755445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1730213459136802169836963 2595320188705203254755445)
                    ·
                      refine ⟨243311267691112805133323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2595320188705203254755445 243311267691112805133323)
                      ·
                        rfl

theorem cell23_473847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_473847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473847 prefixEnd_473847 := by exact prefixLift 473847
  have htrace : WordTrace (prefixWord ++ tailWord_473847) baseStart_473847 baseEnd_473847 := by
    simpa [prefixWord, tailWord_473847, baseEnd_473847] using wordTrace_append hprefix tailTrace_473847
  have hstable : (prefixWord ++ tailWord_473847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473847).length < 2 ^ (prefixWord ++ tailWord_473847).sum := by decide
  have hdescent : baseEnd_473847 < baseStart_473847 := by decide
  rcases family_descends (prefixWord ++ tailWord_473847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473934 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_473934 : Nat := 118140960795 + 473934 * 2 ^ 59
def prefixEnd_473934 : Nat := 4983230072969 + 3 ^ 40 * 473934 * 2
def baseEnd_473934 : Nat := 243355940508053964745423

theorem tailTrace_473934 : CollatzResearch.WordTrace tailWord_473934 prefixEnd_473934 243355940508053964745423 := by
  unfold tailWord_473934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2160724133128191791028607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11523862043350356218819237 2160724133128191791028607)
  ·
    refine ⟨3241086199692287686542911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2160724133128191791028607 3241086199692287686542911)
    ·
      refine ⟨4861629299538431529814367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3241086199692287686542911 4861629299538431529814367)
      ·
        refine ⟨7292443949307647294721551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4861629299538431529814367 7292443949307647294721551)
        ·
          refine ⟨10938665923961470942082327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7292443949307647294721551 10938665923961470942082327)
          ·
            refine ⟨16407998885942206413123491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10938665923961470942082327 16407998885942206413123491)
            ·
              refine ⟨24611998328913309619685237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16407998885942206413123491 24611998328913309619685237)
              ·
                refine ⟨2307374843335622776845491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24611998328913309619685237 2307374843335622776845491)
                ·
                  refine ⟨3461062265003434165268237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307374843335622776845491 3461062265003434165268237)
                  ·
                    refine ⟨1297898349376287811975589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3461062265003434165268237 1297898349376287811975589)
                    ·
                      refine ⟨243355940508053964745423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1297898349376287811975589 243355940508053964745423)
                      ·
                        rfl

theorem cell23_473934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_473934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473934 prefixEnd_473934 := by exact prefixLift 473934
  have htrace : WordTrace (prefixWord ++ tailWord_473934) baseStart_473934 baseEnd_473934 := by
    simpa [prefixWord, tailWord_473934, baseEnd_473934] using wordTrace_append hprefix tailTrace_473934
  have hstable : (prefixWord ++ tailWord_473934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473934).length < 2 ^ (prefixWord ++ tailWord_473934).sum := by decide
  have hdescent : baseEnd_473934 < baseStart_473934 := by decide
  rcases family_descends (prefixWord ++ tailWord_473934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473951 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 2, 4, 2]
def baseStart_473951 : Nat := 118140960795 + 473951 * 2 ^ 59
def prefixEnd_473951 : Nat := 4983230072969 + 3 ^ 40 * 473951 * 2
def baseEnd_473951 : Nat := 243364669679180398232845

theorem tailTrace_473951 : CollatzResearch.WordTrace tailWord_473951 prefixEnd_473951 243364669679180398232845 := by
  unfold tailWord_473951
  simp only [CollatzResearch.WordTrace]
  refine ⟨17286413105963946231597707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11524275403975964154398471 17286413105963946231597707)
  ·
    refine ⟨25929619658945919347396561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17286413105963946231597707 25929619658945919347396561)
    ·
      refine ⟨19447214744209439510547421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25929619658945919347396561 19447214744209439510547421)
      ·
        refine ⟨7292705529078539816455283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19447214744209439510547421 7292705529078539816455283)
        ·
          refine ⟨10939058293617809724682925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7292705529078539816455283 10939058293617809724682925)
          ·
            refine ⟨4102146860106678646756097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10939058293617809724682925 4102146860106678646756097)
            ·
              refine ⟨3076610145080008985067073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4102146860106678646756097 3076610145080008985067073)
              ·
                refine ⟨2307457608810006738800305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3076610145080008985067073 2307457608810006738800305)
                ·
                  refine ⟨1730593206607505054100229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2307457608810006738800305 1730593206607505054100229)
                  ·
                    refine ⟨324486226238907197643793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1730593206607505054100229 324486226238907197643793)
                    ·
                      refine ⟨243364669679180398232845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 324486226238907197643793 243364669679180398232845)
                      ·
                        rfl

theorem cell23_473951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_473951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473951 prefixEnd_473951 := by exact prefixLift 473951
  have htrace : WordTrace (prefixWord ++ tailWord_473951) baseStart_473951 baseEnd_473951 := by
    simpa [prefixWord, tailWord_473951, baseEnd_473951] using wordTrace_append hprefix tailTrace_473951
  have hstable : (prefixWord ++ tailWord_473951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473951).length < 2 ^ (prefixWord ++ tailWord_473951).sum := by decide
  have hdescent : baseEnd_473951 < baseStart_473951 := by decide
  rcases family_descends (prefixWord ++ tailWord_473951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473982 : List Nat := [4, 2, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_473982 : Nat := 118140960795 + 473982 * 2 ^ 59
def prefixEnd_473982 : Nat := 4983230072969 + 3 ^ 40 * 473982 * 2
def baseEnd_473982 : Nat := 81126862526489925648401

theorem tailTrace_473982 : CollatzResearch.WordTrace tailWord_473982 prefixEnd_473982 81126862526489925648401 := by
  unfold tailWord_473982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2160942971106454815747025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11525029179234425683984133 2160942971106454815747025)
  ·
    refine ⟨1620707228329841111810269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2160942971106454815747025 1620707228329841111810269)
    ·
      refine ⟨607765210623690416928851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1620707228329841111810269 607765210623690416928851)
      ·
        refine ⟨911647815935535625393277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607765210623690416928851 911647815935535625393277)
        ·
          refine ⟨341867930975825859522479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 911647815935535625393277 341867930975825859522479)
          ·
            refine ⟨512801896463738789283719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341867930975825859522479 512801896463738789283719)
            ·
              refine ⟨769202844695608183925579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512801896463738789283719 769202844695608183925579)
              ·
                refine ⟨1153804267043412275888369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769202844695608183925579 1153804267043412275888369)
                ·
                  refine ⟨865353200282559206916277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1153804267043412275888369 865353200282559206916277)
                  ·
                    refine ⟨81126862526489925648401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 865353200282559206916277 81126862526489925648401)
                    ·
                      rfl

theorem cell23_473982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_473982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473982 prefixEnd_473982 := by exact prefixLift 473982
  have htrace : WordTrace (prefixWord ++ tailWord_473982) baseStart_473982 baseEnd_473982 := by
    simpa [prefixWord, tailWord_473982, baseEnd_473982] using wordTrace_append hprefix tailTrace_473982
  have hstable : (prefixWord ++ tailWord_473982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473982).length < 2 ^ (prefixWord ++ tailWord_473982).sum := by decide
  have hdescent : baseEnd_473982 < baseStart_473982 := by decide
  rcases family_descends (prefixWord ++ tailWord_473982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473984 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 3]
def baseStart_473984 : Nat := 118140960795 + 473984 * 2 ^ 59
def prefixEnd_473984 : Nat := 4983230072969 + 3 ^ 40 * 473984 * 2
def baseEnd_473984 : Nat := 243381614540778769120193

theorem tailTrace_473984 : CollatzResearch.WordTrace tailWord_473984 prefixEnd_473984 243381614540778769120193 := by
  unfold tailWord_473984
  simp only [CollatzResearch.WordTrace]
  refine ⟨8643808357422196433774503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11525077809896261911699337 8643808357422196433774503)
  ·
    refine ⟨12965712536133294650661755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8643808357422196433774503 12965712536133294650661755)
    ·
      refine ⟨19448568804199941975992633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12965712536133294650661755 19448568804199941975992633)
      ·
        refine ⟨14586426603149956481994475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19448568804199941975992633 14586426603149956481994475)
        ·
          refine ⟨21879639904724934722991713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14586426603149956481994475 21879639904724934722991713)
          ·
            refine ⟨16409729928543701042243785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21879639904724934722991713 16409729928543701042243785)
            ·
              refine ⟨12307297446407775781682839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16409729928543701042243785 12307297446407775781682839)
              ·
                refine ⟨18460946169611663672524259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12307297446407775781682839 18460946169611663672524259)
                ·
                  refine ⟨27691419254417495508786389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18460946169611663672524259 27691419254417495508786389)
                  ·
                    refine ⟨649017638775410050987181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27691419254417495508786389 649017638775410050987181)
                    ·
                      refine ⟨243381614540778769120193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 649017638775410050987181 243381614540778769120193)
                      ·
                        rfl

theorem cell23_473984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_473984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_473984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_473984 prefixEnd_473984 := by exact prefixLift 473984
  have htrace : WordTrace (prefixWord ++ tailWord_473984) baseStart_473984 baseEnd_473984 := by
    simpa [prefixWord, tailWord_473984, baseEnd_473984] using wordTrace_append hprefix tailTrace_473984
  have hstable : (prefixWord ++ tailWord_473984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473984).length < 2 ^ (prefixWord ++ tailWord_473984).sum := by decide
  have hdescent : baseEnd_473984 < baseStart_473984 := by decide
  rcases family_descends (prefixWord ++ tailWord_473984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474001 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 7, 1, 3]
def baseStart_474001 : Nat := 118140960795 + 474001 * 2 ^ 59
def prefixEnd_474001 : Nat := 4983230072969 + 3 ^ 40 * 474001 * 2
def baseEnd_474001 : Nat := 243390343711905202607615

theorem tailTrace_474001 : CollatzResearch.WordTrace tailWord_474001 prefixEnd_474001 243390343711905202607615 := by
  unfold tailWord_474001
  simp only [CollatzResearch.WordTrace]
  refine ⟨17288236755782804770917857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11525491170521869847278571 17288236755782804770917857)
  ·
    refine ⟨12966177566837103578188393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17288236755782804770917857 12966177566837103578188393)
    ·
      refine ⟨9724633175127827683641295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12966177566837103578188393 9724633175127827683641295)
      ·
        refine ⟨14586949762691741525461943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9724633175127827683641295 14586949762691741525461943)
        ·
          refine ⟨21880424644037612288192915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14586949762691741525461943 21880424644037612288192915)
          ·
            refine ⟨32820636966056418432289373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21880424644037612288192915 32820636966056418432289373)
            ·
              refine ⟨12307738862271156912108515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32820636966056418432289373 12307738862271156912108515)
              ·
                refine ⟨18461608293406735368162773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12307738862271156912108515 18461608293406735368162773)
                ·
                  refine ⟨432693944376720360191315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18461608293406735368162773 432693944376720360191315)
                  ·
                    refine ⟨649040916565080540286973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 432693944376720360191315 649040916565080540286973)
                    ·
                      refine ⟨243390343711905202607615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 649040916565080540286973 243390343711905202607615)
                      ·
                        rfl

theorem cell23_474001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 1, 3].length) (baseStart_474001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474001 prefixEnd_474001 := by exact prefixLift 474001
  have htrace : WordTrace (prefixWord ++ tailWord_474001) baseStart_474001 baseEnd_474001 := by
    simpa [prefixWord, tailWord_474001, baseEnd_474001] using wordTrace_append hprefix tailTrace_474001
  have hstable : (prefixWord ++ tailWord_474001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474001).length < 2 ^ (prefixWord ++ tailWord_474001).sum := by decide
  have hdescent : baseEnd_474001 < baseStart_474001 := by decide
  rcases family_descends (prefixWord ++ tailWord_474001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474068 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_474068 : Nat := 118140960795 + 474068 * 2 ^ 59
def prefixEnd_474068 : Nat := 4983230072969 + 3 ^ 40 * 474068 * 2
def baseEnd_474068 : Nat := 81141582305252146823269

theorem tailTrace_474068 : CollatzResearch.WordTrace tailWord_474068 prefixEnd_474068 81141582305252146823269 := by
  unfold tailWord_474068
  simp only [CollatzResearch.WordTrace]
  refine ⟨8645340223270037606803429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11527120297693383475737905 8645340223270037606803429)
  ·
    refine ⟨1621001291863132051275643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8645340223270037606803429 1621001291863132051275643)
    ·
      refine ⟨2431501937794698076913465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1621001291863132051275643 2431501937794698076913465)
      ·
        refine ⟨1823626453346023557685099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2431501937794698076913465 1823626453346023557685099)
        ·
          refine ⟨2735439680019035336527649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1823626453346023557685099 2735439680019035336527649)
          ·
            refine ⟨2051579760014276502395737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2735439680019035336527649 2051579760014276502395737)
            ·
              refine ⟨1538684820010707376796803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2051579760014276502395737 1538684820010707376796803)
              ·
                refine ⟨2308027230016061065195205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1538684820010707376796803 2308027230016061065195205)
                ·
                  refine ⟨432755105628011449724101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2308027230016061065195205 432755105628011449724101)
                  ·
                    refine ⟨81141582305252146823269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 432755105628011449724101 81141582305252146823269)
                    ·
                      rfl

theorem cell23_474068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_474068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474068 prefixEnd_474068 := by exact prefixLift 474068
  have htrace : WordTrace (prefixWord ++ tailWord_474068) baseStart_474068 baseEnd_474068 := by
    simpa [prefixWord, tailWord_474068, baseEnd_474068] using wordTrace_append hprefix tailTrace_474068
  have hstable : (prefixWord ++ tailWord_474068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474068).length < 2 ^ (prefixWord ++ tailWord_474068).sum := by decide
  have hdescent : baseEnd_474068 < baseStart_474068 := by decide
  rcases family_descends (prefixWord ++ tailWord_474068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474069 : List Nat := [1, 3, 2, 3, 3, 1, 3, 2, 1, 1, 3]
def baseStart_474069 : Nat := 118140960795 + 474069 * 2 ^ 59
def prefixEnd_474069 : Nat := 4983230072969 + 3 ^ 40 * 474069 * 2
def baseEnd_474069 : Nat := 243425260396410936557303

theorem tailTrace_474069 : CollatzResearch.WordTrace tailWord_474069 prefixEnd_474069 243425260396410936557303 := by
  unfold tailWord_474069
  simp only [CollatzResearch.WordTrace]
  refine ⟨17290716919536452384393261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11527144613024301589595507 17290716919536452384393261)
  ·
    refine ⟨6484018844826169644147473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17290716919536452384393261 6484018844826169644147473)
    ·
      refine ⟨4863014133619627233110605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6484018844826169644147473 4863014133619627233110605)
      ·
        refine ⟨1823630300107360212416477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4863014133619627233110605 1823630300107360212416477)
        ·
          refine ⟨683861362540260079656179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1823630300107360212416477 683861362540260079656179)
          ·
            refine ⟨1025792043810390119484269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683861362540260079656179 1025792043810390119484269)
            ·
              refine ⟨384672016428896294806601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1025792043810390119484269 384672016428896294806601)
              ·
                refine ⟨288504012321672221104951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384672016428896294806601 288504012321672221104951)
                ·
                  refine ⟨432756018482508331657427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288504012321672221104951 432756018482508331657427)
                  ·
                    refine ⟨649134027723762497486141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 432756018482508331657427 649134027723762497486141)
                    ·
                      refine ⟨243425260396410936557303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 649134027723762497486141 243425260396410936557303)
                      ·
                        rfl

theorem cell23_474069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_474069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474069 prefixEnd_474069 := by exact prefixLift 474069
  have htrace : WordTrace (prefixWord ++ tailWord_474069) baseStart_474069 baseEnd_474069 := by
    simpa [prefixWord, tailWord_474069, baseEnd_474069] using wordTrace_append hprefix tailTrace_474069
  have hstable : (prefixWord ++ tailWord_474069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474069).length < 2 ^ (prefixWord ++ tailWord_474069).sum := by decide
  have hdescent : baseEnd_474069 < baseStart_474069 := by decide
  rcases family_descends (prefixWord ++ tailWord_474069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474095 : List Nat := [1, 1, 2, 1, 4, 5, 1, 2, 1, 2, 3]
def baseStart_474095 : Nat := 118140960795 + 474095 * 2 ^ 59
def prefixEnd_474095 : Nat := 4983230072969 + 3 ^ 40 * 474095 * 2
def baseEnd_474095 : Nat := 243438610893427834832183

theorem tailTrace_474095 : CollatzResearch.WordTrace tailWord_474095 prefixEnd_474095 243438610893427834832183 := by
  unfold tailWord_474095
  simp only [CollatzResearch.WordTrace]
  refine ⟨17291665217442258824839739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11527776811628172549893159 17291665217442258824839739)
  ·
    refine ⟨25937497826163388237259609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17291665217442258824839739 25937497826163388237259609)
    ·
      refine ⟨19453123369622541177944707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25937497826163388237259609 19453123369622541177944707)
      ·
        refine ⟨29179685054433811766917061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19453123369622541177944707 29179685054433811766917061)
        ·
          refine ⟨5471190947706339706296949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29179685054433811766917061 5471190947706339706296949)
          ·
            refine ⟨512924151347469347465339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5471190947706339706296949 512924151347469347465339)
            ·
              refine ⟨769386227021204021198009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512924151347469347465339 769386227021204021198009)
              ·
                refine ⟨577039670265903015898507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 769386227021204021198009 577039670265903015898507)
                ·
                  refine ⟨865559505398854523847761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577039670265903015898507 865559505398854523847761)
                  ·
                    refine ⟨649169629049140892885821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 865559505398854523847761 649169629049140892885821)
                    ·
                      refine ⟨243438610893427834832183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 649169629049140892885821 243438610893427834832183)
                      ·
                        rfl

theorem cell23_474095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 2, 3].length) (baseStart_474095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474095 prefixEnd_474095 := by exact prefixLift 474095
  have htrace : WordTrace (prefixWord ++ tailWord_474095) baseStart_474095 baseEnd_474095 := by
    simpa [prefixWord, tailWord_474095, baseEnd_474095] using wordTrace_append hprefix tailTrace_474095
  have hstable : (prefixWord ++ tailWord_474095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474095).length < 2 ^ (prefixWord ++ tailWord_474095).sum := by decide
  have hdescent : baseEnd_474095 < baseStart_474095 := by decide
  rcases family_descends (prefixWord ++ tailWord_474095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474108 : List Nat := [2, 2, 2, 1, 2, 4, 1, 2, 1, 3, 3]
def baseStart_474108 : Nat := 118140960795 + 474108 * 2 ^ 59
def prefixEnd_474108 : Nat := 4983230072969 + 3 ^ 40 * 474108 * 2
def baseEnd_474108 : Nat := 243445286141936283969623

theorem tailTrace_474108 : CollatzResearch.WordTrace tailWord_474108 prefixEnd_474108 243445286141936283969623 := by
  unfold tailWord_474108
  simp only [CollatzResearch.WordTrace]
  refine ⟨8646069683197581022531489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11528092910930108030041985 8646069683197581022531489)
  ·
    refine ⟨6484552262398185766898617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8646069683197581022531489 6484552262398185766898617)
    ·
      refine ⟨4863414196798639325173963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6484552262398185766898617 4863414196798639325173963)
      ·
        refine ⟨7295121295197958987760945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4863414196798639325173963 7295121295197958987760945)
        ·
          refine ⟨5471340971398469240820709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7295121295197958987760945 5471340971398469240820709)
          ·
            refine ⟨1025876432137212982653883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5471340971398469240820709 1025876432137212982653883)
            ·
              refine ⟨1538814648205819473980825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025876432137212982653883 1538814648205819473980825)
              ·
                refine ⟨1154110986154364605485619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1538814648205819473980825 1154110986154364605485619)
                ·
                  refine ⟨1731166479231546908228429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1154110986154364605485619 1731166479231546908228429)
                  ·
                    refine ⟨649187429711830090585661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1731166479231546908228429 649187429711830090585661)
                    ·
                      refine ⟨243445286141936283969623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 649187429711830090585661 243445286141936283969623)
                      ·
                        rfl

theorem cell23_474108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_474108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474108 prefixEnd_474108 := by exact prefixLift 474108
  have htrace : WordTrace (prefixWord ++ tailWord_474108) baseStart_474108 baseEnd_474108 := by
    simpa [prefixWord, tailWord_474108, baseEnd_474108] using wordTrace_append hprefix tailTrace_474108
  have hstable : (prefixWord ++ tailWord_474108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474108).length < 2 ^ (prefixWord ++ tailWord_474108).sum := by decide
  have hdescent : baseEnd_474108 < baseStart_474108 := by decide
  rcases family_descends (prefixWord ++ tailWord_474108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474126 : List Nat := [4, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2]
def baseStart_474126 : Nat := 118140960795 + 474126 * 2 ^ 59
def prefixEnd_474126 : Nat := 4983230072969 + 3 ^ 40 * 474126 * 2
def baseEnd_474126 : Nat := 243454528793717213544541

theorem tailTrace_474126 : CollatzResearch.WordTrace tailWord_474126 prefixEnd_474126 243454528793717213544541 := by
  unfold tailWord_474126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2161599485041243889902279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11528530586886634079478821 2161599485041243889902279)
  ·
    refine ⟨3242399227561865834853419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2161599485041243889902279 3242399227561865834853419)
    ·
      refine ⟨4863598841342798752280129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3242399227561865834853419 4863598841342798752280129)
      ·
        refine ⟨3647699131007099064210097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4863598841342798752280129 3647699131007099064210097)
        ·
          refine ⟨2735774348255324298157573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3647699131007099064210097 2735774348255324298157573)
          ·
            refine ⟨512957690297873305904545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2735774348255324298157573 512957690297873305904545)
            ·
              refine ⟨384718267723404979428409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512957690297873305904545 384718267723404979428409)
              ·
                refine ⟨288538700792553734571307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384718267723404979428409 288538700792553734571307)
                ·
                  refine ⟨432808051188830601856961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288538700792553734571307 432808051188830601856961)
                  ·
                    refine ⟨324606038391622951392721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 432808051188830601856961 324606038391622951392721)
                    ·
                      refine ⟨243454528793717213544541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 324606038391622951392721 243454528793717213544541)
                      ·
                        rfl

theorem cell23_474126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_474126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474126 prefixEnd_474126 := by exact prefixLift 474126
  have htrace : WordTrace (prefixWord ++ tailWord_474126) baseStart_474126 baseEnd_474126 := by
    simpa [prefixWord, tailWord_474126, baseEnd_474126] using wordTrace_append hprefix tailTrace_474126
  have hstable : (prefixWord ++ tailWord_474126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474126).length < 2 ^ (prefixWord ++ tailWord_474126).sum := by decide
  have hdescent : baseEnd_474126 < baseStart_474126 := by decide
  rcases family_descends (prefixWord ++ tailWord_474126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474135 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 3, 3, 2]
def baseStart_474135 : Nat := 118140960795 + 474135 * 2 ^ 59
def prefixEnd_474135 : Nat := 4983230072969 + 3 ^ 40 * 474135 * 2
def baseEnd_474135 : Nat := 243459150119607678331999

theorem tailTrace_474135 : CollatzResearch.WordTrace tailWord_474135 prefixEnd_474135 243459150119607678331999 := by
  unfold tailWord_474135
  simp only [CollatzResearch.WordTrace]
  refine ⟨17293124137297345656295859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11528749424864897104197239 17293124137297345656295859)
  ·
    refine ⟨25939686205946018484443789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17293124137297345656295859 25939686205946018484443789)
    ·
      refine ⟨9727382327229756931666421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25939686205946018484443789 9727382327229756931666421)
      ·
        refine ⟨911942093177789712343727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9727382327229756931666421 911942093177789712343727)
        ·
          refine ⟨1367913139766684568515591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911942093177789712343727 1367913139766684568515591)
          ·
            refine ⟨2051869709650026852773387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367913139766684568515591 2051869709650026852773387)
            ·
              refine ⟨3077804564475040279160081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2051869709650026852773387 3077804564475040279160081)
              ·
                refine ⟨2308353423356280209370061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3077804564475040279160081 2308353423356280209370061)
                ·
                  refine ⟨865632533758605078513773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2308353423356280209370061 865632533758605078513773)
                  ·
                    refine ⟨324612200159476904442665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 865632533758605078513773 324612200159476904442665)
                    ·
                      refine ⟨243459150119607678331999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 324612200159476904442665 243459150119607678331999)
                      ·
                        rfl

theorem cell23_474135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_474135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474135 prefixEnd_474135 := by exact prefixLift 474135
  have htrace : WordTrace (prefixWord ++ tailWord_474135) baseStart_474135 baseEnd_474135 := by
    simpa [prefixWord, tailWord_474135, baseEnd_474135] using wordTrace_append hprefix tailTrace_474135
  have hstable : (prefixWord ++ tailWord_474135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474135).length < 2 ^ (prefixWord ++ tailWord_474135).sum := by decide
  have hdescent : baseEnd_474135 < baseStart_474135 := by decide
  rcases family_descends (prefixWord ++ tailWord_474135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474161 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 1, 4, 4]
def baseStart_474161 : Nat := 118140960795 + 474161 * 2 ^ 59
def prefixEnd_474161 : Nat := 4983230072969 + 3 ^ 40 * 474161 * 2
def baseEnd_474161 : Nat := 243472500616624576606879

theorem tailTrace_474161 : CollatzResearch.WordTrace tailWord_474161 prefixEnd_474161 243472500616624576606879 := by
  unfold tailWord_474161
  simp only [CollatzResearch.WordTrace]
  refine ⟨17294072435203152096742337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11529381623468768064494891 17294072435203152096742337)
  ·
    refine ⟨12970554326402364072556753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17294072435203152096742337 12970554326402364072556753)
    ·
      refine ⟨9727915744801773054417565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12970554326402364072556753 9727915744801773054417565)
      ·
        refine ⟨3647968404300664895406587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9727915744801773054417565 3647968404300664895406587)
        ·
          refine ⟨5471952606450997343109881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3647968404300664895406587 5471952606450997343109881)
          ·
            refine ⟨4103964454838248007332411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5471952606450997343109881 4103964454838248007332411)
            ·
              refine ⟨6155946682257372010998617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4103964454838248007332411 6155946682257372010998617)
              ·
                refine ⟨4616960011693029008248963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6155946682257372010998617 4616960011693029008248963)
                ·
                  refine ⟨6925440017539543512373445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4616960011693029008248963 6925440017539543512373445)
                  ·
                    refine ⟨1298520003288664408570021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6925440017539543512373445 1298520003288664408570021)
                    ·
                      refine ⟨243472500616624576606879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1298520003288664408570021 243472500616624576606879)
                      ·
                        rfl

theorem cell23_474161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_474161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474161 prefixEnd_474161 := by exact prefixLift 474161
  have htrace : WordTrace (prefixWord ++ tailWord_474161) baseStart_474161 baseEnd_474161 := by
    simpa [prefixWord, tailWord_474161, baseEnd_474161] using wordTrace_append hprefix tailTrace_474161
  have hstable : (prefixWord ++ tailWord_474161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474161).length < 2 ^ (prefixWord ++ tailWord_474161).sum := by decide
  have hdescent : baseEnd_474161 < baseStart_474161 := by decide
  rcases family_descends (prefixWord ++ tailWord_474161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474165 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 4, 2, 2]
def baseStart_474165 : Nat := 118140960795 + 474165 * 2 ^ 59
def prefixEnd_474165 : Nat := 4983230072969 + 3 ^ 40 * 474165 * 2
def baseEnd_474165 : Nat := 243474554539242560956861

theorem tailTrace_474165 : CollatzResearch.WordTrace tailWord_474165 prefixEnd_474165 243474554539242560956861 := by
  unfold tailWord_474165
  simp only [CollatzResearch.WordTrace]
  refine ⟨17294218327188660779887949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11529478884792440519925299 17294218327188660779887949)
  ·
    refine ⟨6485331872695747792457981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17294218327188660779887949 6485331872695747792457981)
    ·
      refine ⟨2431999452260905422171743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6485331872695747792457981 2431999452260905422171743)
      ·
        refine ⟨3647999178391358133257615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2431999452260905422171743 3647999178391358133257615)
        ·
          refine ⟨5471998767587037199886423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3647999178391358133257615 5471998767587037199886423)
          ·
            refine ⟨8207998151380555799829635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5471998767587037199886423 8207998151380555799829635)
            ·
              refine ⟨12311997227070833699744453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8207998151380555799829635 12311997227070833699744453)
              ·
                refine ⟨2308499480075781318702085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12311997227070833699744453 2308499480075781318702085)
                ·
                  refine ⟨432843652514208997256641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2308499480075781318702085 432843652514208997256641)
                  ·
                    refine ⟨324632739385656747942481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 432843652514208997256641 324632739385656747942481)
                    ·
                      refine ⟨243474554539242560956861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 324632739385656747942481 243474554539242560956861)
                      ·
                        rfl

theorem cell23_474165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_474165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474165 prefixEnd_474165 := by exact prefixLift 474165
  have htrace : WordTrace (prefixWord ++ tailWord_474165) baseStart_474165 baseEnd_474165 := by
    simpa [prefixWord, tailWord_474165, baseEnd_474165] using wordTrace_append hprefix tailTrace_474165
  have hstable : (prefixWord ++ tailWord_474165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474165).length < 2 ^ (prefixWord ++ tailWord_474165).sum := by decide
  have hdescent : baseEnd_474165 < baseStart_474165 := by decide
  rcases family_descends (prefixWord ++ tailWord_474165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474169 : List Nat := [1, 2, 1, 5, 2, 3, 2, 1, 1, 3, 2]
def baseStart_474169 : Nat := 118140960795 + 474169 * 2 ^ 59
def prefixEnd_474169 : Nat := 4983230072969 + 3 ^ 40 * 474169 * 2
def baseEnd_474169 : Nat := 243476608461860545306843

theorem tailTrace_474169 : CollatzResearch.WordTrace tailWord_474169 prefixEnd_474169 243476608461860545306843 := by
  unfold tailWord_474169
  simp only [CollatzResearch.WordTrace]
  refine ⟨17294364219174169463033561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11529576146116112975355707 17294364219174169463033561)
  ·
    refine ⟨12970773164380627097275171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17294364219174169463033561 12970773164380627097275171)
    ·
      refine ⟨19456159746570940645912757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12970773164380627097275171 19456159746570940645912757)
      ·
        refine ⟨1824014976241025685554321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19456159746570940645912757 1824014976241025685554321)
        ·
          refine ⟨1368011232180769264165741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1824014976241025685554321 1368011232180769264165741)
          ·
            refine ⟨513004212067788474062153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1368011232180769264165741 513004212067788474062153)
            ·
              refine ⟨384753159050841355546615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513004212067788474062153 384753159050841355546615)
              ·
                refine ⟨577129738576262033319923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384753159050841355546615 577129738576262033319923)
                ·
                  refine ⟨865694607864393049979885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577129738576262033319923 865694607864393049979885)
                  ·
                    refine ⟨324635477949147393742457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 865694607864393049979885 324635477949147393742457)
                    ·
                      refine ⟨243476608461860545306843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 324635477949147393742457 243476608461860545306843)
                      ·
                        rfl

theorem cell23_474169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_474169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474169 prefixEnd_474169 := by exact prefixLift 474169
  have htrace : WordTrace (prefixWord ++ tailWord_474169) baseStart_474169 baseEnd_474169 := by
    simpa [prefixWord, tailWord_474169, baseEnd_474169] using wordTrace_append hprefix tailTrace_474169
  have hstable : (prefixWord ++ tailWord_474169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474169).length < 2 ^ (prefixWord ++ tailWord_474169).sum := by decide
  have hdescent : baseEnd_474169 < baseStart_474169 := by decide
  rcases family_descends (prefixWord ++ tailWord_474169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474201 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 6, 5]
def baseStart_474201 : Nat := 118140960795 + 474201 * 2 ^ 59
def prefixEnd_474201 : Nat := 4983230072969 + 3 ^ 40 * 474201 * 2
def baseEnd_474201 : Nat := 81164346614268140035565

theorem tailTrace_474201 : CollatzResearch.WordTrace tailWord_474201 prefixEnd_474201 81164346614268140035565 := by
  unfold tailWord_474201
  simp only [CollatzResearch.WordTrace]
  refine ⟨17295531355058238928198457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11530354236705492618798971 17295531355058238928198457)
  ·
    refine ⟨12971648516293679196148843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17295531355058238928198457 12971648516293679196148843)
    ·
      refine ⟨19457472774440518794223265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12971648516293679196148843 19457472774440518794223265)
      ·
        refine ⟨14593104580830389095667449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19457472774440518794223265 14593104580830389095667449)
        ·
          refine ⟨10944828435622791821750587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14593104580830389095667449 10944828435622791821750587)
          ·
            refine ⟨16417242653434187732625881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10944828435622791821750587 16417242653434187732625881)
            ·
              refine ⟨12312931990075640799469411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16417242653434187732625881 12312931990075640799469411)
              ·
                refine ⟨18469397985113461199204117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12312931990075640799469411 18469397985113461199204117)
                ·
                  refine ⟨865753030552193493712693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18469397985113461199204117 865753030552193493712693)
                  ·
                    refine ⟨81164346614268140035565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 865753030552193493712693 81164346614268140035565)
                    ·
                      rfl

theorem cell23_474201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 5].length) (baseStart_474201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474201 prefixEnd_474201 := by exact prefixLift 474201
  have htrace : WordTrace (prefixWord ++ tailWord_474201) baseStart_474201 baseEnd_474201 := by
    simpa [prefixWord, tailWord_474201, baseEnd_474201] using wordTrace_append hprefix tailTrace_474201
  have hstable : (prefixWord ++ tailWord_474201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474201).length < 2 ^ (prefixWord ++ tailWord_474201).sum := by decide
  have hdescent : baseEnd_474201 < baseStart_474201 := by decide
  rcases family_descends (prefixWord ++ tailWord_474201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474211 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 5]
def baseStart_474211 : Nat := 118140960795 + 474211 * 2 ^ 59
def prefixEnd_474211 : Nat := 4983230072969 + 3 ^ 40 * 474211 * 2
def baseEnd_474211 : Nat := 243498174649349380981649

theorem tailTrace_474211 : CollatzResearch.WordTrace tailWord_474211 prefixEnd_474211 243498174649349380981649 := by
  unfold tailWord_474211
  simp only [CollatzResearch.WordTrace]
  refine ⟨17295896085022010636062487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11530597390014673757374991 17295896085022010636062487)
  ·
    refine ⟨25943844127533015954093731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17295896085022010636062487 25943844127533015954093731)
    ·
      refine ⟨38915766191299523931140597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25943844127533015954093731 38915766191299523931140597)
      ·
        refine ⟨3648353080434330368544431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38915766191299523931140597 3648353080434330368544431)
        ·
          refine ⟨5472529620651495552816647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3648353080434330368544431 5472529620651495552816647)
          ·
            refine ⟨8208794430977243329224971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5472529620651495552816647 8208794430977243329224971)
            ·
              refine ⟨12313191646465864993837457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8208794430977243329224971 12313191646465864993837457)
              ·
                refine ⟨9234893734849398745378093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12313191646465864993837457 9234893734849398745378093)
                ·
                  refine ⟨3463085150568524529516785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9234893734849398745378093 3463085150568524529516785)
                  ·
                    refine ⟨2597313862926393397137589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3463085150568524529516785 2597313862926393397137589)
                    ·
                      refine ⟨243498174649349380981649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2597313862926393397137589 243498174649349380981649)
                      ·
                        rfl

theorem cell23_474211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_474211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474211 prefixEnd_474211 := by exact prefixLift 474211
  have htrace : WordTrace (prefixWord ++ tailWord_474211) baseStart_474211 baseEnd_474211 := by
    simpa [prefixWord, tailWord_474211, baseEnd_474211] using wordTrace_append hprefix tailTrace_474211
  have hstable : (prefixWord ++ tailWord_474211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474211).length < 2 ^ (prefixWord ++ tailWord_474211).sum := by decide
  have hdescent : baseEnd_474211 < baseStart_474211 := by decide
  rcases family_descends (prefixWord ++ tailWord_474211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474218 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 1, 7]
def baseStart_474218 : Nat := 118140960795 + 474218 * 2 ^ 59
def prefixEnd_474218 : Nat := 4983230072969 + 3 ^ 40 * 474218 * 2
def baseEnd_474218 : Nat := 81167256337976951198039

theorem tailTrace_474218 : CollatzResearch.WordTrace tailWord_474218 prefixEnd_474218 81167256337976951198039 := by
  unfold tailWord_474218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4324037848999162707891827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11530767597331100554378205 4324037848999162707891827)
  ·
    refine ⟨6486056773498744061837741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4324037848999162707891827 6486056773498744061837741)
    ·
      refine ⟨2432271290062029023189153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6486056773498744061837741 2432271290062029023189153)
      ·
        refine ⟨1824203467546521767391865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2432271290062029023189153 1824203467546521767391865)
        ·
          refine ⟨1368152600659891325543899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1824203467546521767391865 1368152600659891325543899)
          ·
            refine ⟨2052228900989836988315849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368152600659891325543899 2052228900989836988315849)
            ·
              refine ⟨1539171675742377741236887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2052228900989836988315849 1539171675742377741236887)
              ·
                refine ⟨2308757513613566611855331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539171675742377741236887 2308757513613566611855331)
                ·
                  refine ⟨3463136270420349917782997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2308757513613566611855331 3463136270420349917782997)
                  ·
                    refine ⟨81167256337976951198039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3463136270420349917782997 81167256337976951198039)
                    ·
                      rfl

theorem cell23_474218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_474218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474218 prefixEnd_474218 := by exact prefixLift 474218
  have htrace : WordTrace (prefixWord ++ tailWord_474218) baseStart_474218 baseEnd_474218 := by
    simpa [prefixWord, tailWord_474218, baseEnd_474218] using wordTrace_append hprefix tailTrace_474218
  have hstable : (prefixWord ++ tailWord_474218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474218).length < 2 ^ (prefixWord ++ tailWord_474218).sum := by decide
  have hdescent : baseEnd_474218 < baseStart_474218 := by decide
  rcases family_descends (prefixWord ++ tailWord_474218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474222 : List Nat := [4, 1, 2, 2, 1, 4, 1, 3, 5]
def baseStart_474222 : Nat := 118140960795 + 474222 * 2 ^ 59
def prefixEnd_474222 : Nat := 4983230072969 + 3 ^ 40 * 474222 * 2
def baseEnd_474222 : Nat := 27055980326283204216011

theorem tailTrace_474222 : CollatzResearch.WordTrace tailWord_474222 prefixEnd_474222 27055980326283204216011 := by
  unfold tailWord_474222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2162037160997769939339115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11530864858654773009808613 2162037160997769939339115)
  ·
    refine ⟨3243055741496654909008673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2162037160997769939339115 3243055741496654909008673)
    ·
      refine ⟨2432291806122491181756505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3243055741496654909008673 2432291806122491181756505)
      ·
        refine ⟨1824218854591868386317379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2432291806122491181756505 1824218854591868386317379)
        ·
          refine ⟨2736328281887802579476069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1824218854591868386317379 2736328281887802579476069)
          ·
            refine ⟨513061552853962983651763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2736328281887802579476069 513061552853962983651763)
            ·
              refine ⟨769592329280944475477645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513061552853962983651763 769592329280944475477645)
              ·
                refine ⟨288597123480354178304117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 769592329280944475477645 288597123480354178304117)
                ·
                  refine ⟨27055980326283204216011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 288597123480354178304117 27055980326283204216011)
                  ·
                    rfl

theorem cell23_474222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_474222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474222 prefixEnd_474222 := by exact prefixLift 474222
  have htrace : WordTrace (prefixWord ++ tailWord_474222) baseStart_474222 baseEnd_474222 := by
    simpa [prefixWord, tailWord_474222, baseEnd_474222] using wordTrace_append hprefix tailTrace_474222
  have hstable : (prefixWord ++ tailWord_474222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474222).length < 2 ^ (prefixWord ++ tailWord_474222).sum := by decide
  have hdescent : baseEnd_474222 < baseStart_474222 := by decide
  rcases family_descends (prefixWord ++ tailWord_474222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474251 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 6]
def baseStart_474251 : Nat := 118140960795 + 474251 * 2 ^ 59
def prefixEnd_474251 : Nat := 4983230072969 + 3 ^ 40 * 474251 * 2
def baseEnd_474251 : Nat := 243518713875529224481465

theorem tailTrace_474251 : CollatzResearch.WordTrace tailWord_474251 prefixEnd_474251 243518713875529224481465 := by
  unfold tailWord_474251
  simp only [CollatzResearch.WordTrace]
  refine ⟨17297355004877097467518607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11531570003251398311679071 17297355004877097467518607)
  ·
    refine ⟨25946032507315646201277911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17297355004877097467518607 25946032507315646201277911)
    ·
      refine ⟨38919048760973469301916867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25946032507315646201277911 38919048760973469301916867)
      ·
        refine ⟨58378573141460203952875301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38919048760973469301916867 58378573141460203952875301)
        ·
          refine ⟨10945982464023788241164119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58378573141460203952875301 10945982464023788241164119)
          ·
            refine ⟨16418973696035682361746179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10945982464023788241164119 16418973696035682361746179)
            ·
              refine ⟨24628460544053523542619269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16418973696035682361746179 24628460544053523542619269)
              ·
                refine ⟨4617836352010035664241113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24628460544053523542619269 4617836352010035664241113)
                ·
                  refine ⟨3463377264007526748180835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4617836352010035664241113 3463377264007526748180835)
                  ·
                    refine ⟨5195065896011290122271253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3463377264007526748180835 5195065896011290122271253)
                    ·
                      refine ⟨243518713875529224481465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5195065896011290122271253 243518713875529224481465)
                      ·
                        rfl

theorem cell23_474251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 6].length) (baseStart_474251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474251 prefixEnd_474251 := by exact prefixLift 474251
  have htrace : WordTrace (prefixWord ++ tailWord_474251) baseStart_474251 baseEnd_474251 := by
    simpa [prefixWord, tailWord_474251, baseEnd_474251] using wordTrace_append hprefix tailTrace_474251
  have hstable : (prefixWord ++ tailWord_474251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474251).length < 2 ^ (prefixWord ++ tailWord_474251).sum := by decide
  have hdescent : baseEnd_474251 < baseStart_474251 := by decide
  rcases family_descends (prefixWord ++ tailWord_474251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474261 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 10]
def baseStart_474261 : Nat := 118140960795 + 474261 * 2 ^ 59
def prefixEnd_474261 : Nat := 4983230072969 + 3 ^ 40 * 474261 * 2
def baseEnd_474261 : Nat := 27058205409119353928491

theorem tailTrace_474261 : CollatzResearch.WordTrace tailWord_474261 prefixEnd_474261 27058205409119353928491 := by
  unfold tailWord_474261
  simp only [CollatzResearch.WordTrace]
  refine ⟨17297719734840869175382637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11531813156560579450255091 17297719734840869175382637)
  ·
    refine ⟨6486644900565325940768489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17297719734840869175382637 6486644900565325940768489)
    ·
      refine ⟨4864983675423994455576367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6486644900565325940768489 4864983675423994455576367)
      ·
        refine ⟨7297475513135991683364551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4864983675423994455576367 7297475513135991683364551)
        ·
          refine ⟨10946213269703987525046827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7297475513135991683364551 10946213269703987525046827)
          ·
            refine ⟨16419319904555981287570241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10946213269703987525046827 16419319904555981287570241)
            ·
              refine ⟨12314489928416985965677681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16419319904555981287570241 12314489928416985965677681)
              ·
                refine ⟨9235867446312739474258261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12314489928416985965677681 9235867446312739474258261)
                ·
                  refine ⟨27058205409119353928491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 9235867446312739474258261 27058205409119353928491)
                  ·
                    rfl

theorem cell23_474261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 10].length) (baseStart_474261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474261 prefixEnd_474261 := by exact prefixLift 474261
  have htrace : WordTrace (prefixWord ++ tailWord_474261) baseStart_474261 baseEnd_474261 := by
    simpa [prefixWord, tailWord_474261, baseEnd_474261] using wordTrace_append hprefix tailTrace_474261
  have hstable : (prefixWord ++ tailWord_474261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474261).length < 2 ^ (prefixWord ++ tailWord_474261).sum := by decide
  have hdescent : baseEnd_474261 < baseStart_474261 := by decide
  rcases family_descends (prefixWord ++ tailWord_474261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474281 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 5, 2, 6]
def baseStart_474281 : Nat := 118140960795 + 474281 * 2 ^ 59
def prefixEnd_474281 : Nat := 4983230072969 + 3 ^ 40 * 474281 * 2
def baseEnd_474281 : Nat := 243534118295164107106327

theorem tailTrace_474281 : CollatzResearch.WordTrace tailWord_474281 prefixEnd_474281 243534118295164107106327 := by
  unfold tailWord_474281
  simp only [CollatzResearch.WordTrace]
  refine ⟨17298449194768412591110697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11532299463178941727407131 17298449194768412591110697)
  ·
    refine ⟨12973836896076309443333023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17298449194768412591110697 12973836896076309443333023)
    ·
      refine ⟨19460755344114464164999535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12973836896076309443333023 19460755344114464164999535)
      ·
        refine ⟨29191133016171696247499303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19460755344114464164999535 29191133016171696247499303)
        ·
          refine ⟨43786699524257544371248955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29191133016171696247499303 43786699524257544371248955)
          ·
            refine ⟨65680049286386316556873433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43786699524257544371248955 65680049286386316556873433)
            ·
              refine ⟨49260036964789737417655075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65680049286386316556873433 49260036964789737417655075)
              ·
                refine ⟨73890055447184606126482613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49260036964789737417655075 73890055447184606126482613)
                ·
                  refine ⟨6927192698173556824357745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73890055447184606126482613 6927192698173556824357745)
                  ·
                    refine ⟨5195394523630167618268309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6927192698173556824357745 5195394523630167618268309)
                    ·
                      refine ⟨243534118295164107106327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5195394523630167618268309 243534118295164107106327)
                      ·
                        rfl

theorem cell23_474281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_474281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474281 prefixEnd_474281 := by exact prefixLift 474281
  have htrace : WordTrace (prefixWord ++ tailWord_474281) baseStart_474281 baseEnd_474281 := by
    simpa [prefixWord, tailWord_474281, baseEnd_474281] using wordTrace_append hprefix tailTrace_474281
  have hstable : (prefixWord ++ tailWord_474281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474281).length < 2 ^ (prefixWord ++ tailWord_474281).sum := by decide
  have hdescent : baseEnd_474281 < baseStart_474281 := by decide
  rcases family_descends (prefixWord ++ tailWord_474281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474306 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_474306 : Nat := 118140960795 + 474306 * 2 ^ 59
def prefixEnd_474306 : Nat := 4983230072969 + 3 ^ 40 * 474306 * 2
def baseEnd_474306 : Nat := 243546955311526509293713

theorem tailTrace_474306 : CollatzResearch.WordTrace tailWord_474306 prefixEnd_474306 243546955311526509293713 := by
  unfold tailWord_474306
  simp only [CollatzResearch.WordTrace]
  refine ⟨4324840254919460465192693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11532907346451894573847181 4324840254919460465192693)
  ·
    refine ⟨405453773898699418611815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4324840254919460465192693 405453773898699418611815)
    ·
      refine ⟨608180660848049127917723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405453773898699418611815 608180660848049127917723)
      ·
        refine ⟨912270991272073691876585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608180660848049127917723 912270991272073691876585)
        ·
          refine ⟨684203243454055268907439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 912270991272073691876585 684203243454055268907439)
          ·
            refine ⟨1026304865181082903361159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684203243454055268907439 1026304865181082903361159)
            ·
              refine ⟨1539457297771624355041739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026304865181082903361159 1539457297771624355041739)
              ·
                refine ⟨2309185946657436532562609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539457297771624355041739 2309185946657436532562609)
                ·
                  refine ⟨1731889459993077399421957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2309185946657436532562609 1731889459993077399421957)
                  ·
                    refine ⟨324729273748702012391617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1731889459993077399421957 324729273748702012391617)
                    ·
                      refine ⟨243546955311526509293713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 324729273748702012391617 243546955311526509293713)
                      ·
                        rfl

theorem cell23_474306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_474306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474306 prefixEnd_474306 := by exact prefixLift 474306
  have htrace : WordTrace (prefixWord ++ tailWord_474306) baseStart_474306 baseEnd_474306 := by
    simpa [prefixWord, tailWord_474306, baseEnd_474306] using wordTrace_append hprefix tailTrace_474306
  have hstable : (prefixWord ++ tailWord_474306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474306).length < 2 ^ (prefixWord ++ tailWord_474306).sum := by decide
  have hdescent : baseEnd_474306 < baseStart_474306 := by decide
  rcases family_descends (prefixWord ++ tailWord_474306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474322 : List Nat := [3, 2, 2, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_474322 : Nat := 118140960795 + 474322 * 2 ^ 59
def prefixEnd_474322 : Nat := 4983230072969 + 3 ^ 40 * 474322 * 2
def baseEnd_474322 : Nat := 243555171001998446693639

theorem tailTrace_474322 : CollatzResearch.WordTrace tailWord_474322 prefixEnd_474322 243555171001998446693639 := by
  unfold tailWord_474322
  simp only [CollatzResearch.WordTrace]
  refine ⟨4324986146904969148338305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11533296391746584395568813 4324986146904969148338305)
  ·
    refine ⟨3243739610178726861253729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4324986146904969148338305 3243739610178726861253729)
    ·
      refine ⟨2432804707634045145940297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3243739610178726861253729 2432804707634045145940297)
      ·
        refine ⟨1824603530725533859455223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2432804707634045145940297 1824603530725533859455223)
        ·
          refine ⟨2736905296088300789182835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1824603530725533859455223 2736905296088300789182835)
          ·
            refine ⟨4105357944132451183774253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2736905296088300789182835 4105357944132451183774253)
            ·
              refine ⟨1539509229049669193915345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4105357944132451183774253 1539509229049669193915345)
              ·
                refine ⟨1154631921787251895436509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1539509229049669193915345 1154631921787251895436509)
                ·
                  refine ⟨432986970670219460788691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1154631921787251895436509 432986970670219460788691)
                  ·
                    refine ⟨649480456005329191183037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 432986970670219460788691 649480456005329191183037)
                    ·
                      refine ⟨243555171001998446693639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 649480456005329191183037 243555171001998446693639)
                      ·
                        rfl

theorem cell23_474322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_474322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474322 prefixEnd_474322 := by exact prefixLift 474322
  have htrace : WordTrace (prefixWord ++ tailWord_474322) baseStart_474322 baseEnd_474322 := by
    simpa [prefixWord, tailWord_474322, baseEnd_474322] using wordTrace_append hprefix tailTrace_474322
  have hstable : (prefixWord ++ tailWord_474322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474322).length < 2 ^ (prefixWord ++ tailWord_474322).sum := by decide
  have hdescent : baseEnd_474322 < baseStart_474322 := by decide
  rcases family_descends (prefixWord ++ tailWord_474322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474325 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 3, 5]
def baseStart_474325 : Nat := 118140960795 + 474325 * 2 ^ 59
def prefixEnd_474325 : Nat := 4983230072969 + 3 ^ 40 * 474325 * 2
def baseEnd_474325 : Nat := 81185570481320644985375

theorem tailTrace_474325 : CollatzResearch.WordTrace tailWord_474325 prefixEnd_474325 81185570481320644985375 := by
  unfold tailWord_474325
  simp only [CollatzResearch.WordTrace]
  refine ⟨17300054006609008105712429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11533369337739338737141619 17300054006609008105712429)
  ·
    refine ⟨6487520252478378039642161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17300054006609008105712429 6487520252478378039642161)
    ·
      refine ⟨4865640189358783529731621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6487520252478378039642161 4865640189358783529731621)
      ·
        refine ⟨912307535504771911824679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4865640189358783529731621 912307535504771911824679)
        ·
          refine ⟨1368461303257157867737019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912307535504771911824679 1368461303257157867737019)
          ·
            refine ⟨2052691954885736801605529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368461303257157867737019 2052691954885736801605529)
            ·
              refine ⟨1539518966164302601204147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2052691954885736801605529 1539518966164302601204147)
              ·
                refine ⟨2309278449246453901806221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539518966164302601204147 2309278449246453901806221)
                ·
                  refine ⟨865979418467420213177333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2309278449246453901806221 865979418467420213177333)
                  ·
                    refine ⟨81185570481320644985375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 865979418467420213177333 81185570481320644985375)
                    ·
                      rfl

theorem cell23_474325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_474325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474325 prefixEnd_474325 := by exact prefixLift 474325
  have htrace : WordTrace (prefixWord ++ tailWord_474325) baseStart_474325 baseEnd_474325 := by
    simpa [prefixWord, tailWord_474325, baseEnd_474325] using wordTrace_append hprefix tailTrace_474325
  have hstable : (prefixWord ++ tailWord_474325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474325).length < 2 ^ (prefixWord ++ tailWord_474325).sum := by decide
  have hdescent : baseEnd_474325 < baseStart_474325 := by decide
  rcases family_descends (prefixWord ++ tailWord_474325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474326 : List Nat := [5, 2, 1, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_474326 : Nat := 118140960795 + 474326 * 2 ^ 59
def prefixEnd_474326 : Nat := 4983230072969 + 3 ^ 40 * 474326 * 2
def baseEnd_474326 : Nat := 243557224924616431043621

theorem tailTrace_474326 : CollatzResearch.WordTrace tailWord_474326 prefixEnd_474326 243557224924616431043621 := by
  unfold tailWord_474326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1081255654975336579781177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11533393653070256850999221 1081255654975336579781177)
  ·
    refine ⟨810941741231502434835883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1081255654975336579781177 810941741231502434835883)
    ·
      refine ⟨1216412611847253652253825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 810941741231502434835883 1216412611847253652253825)
      ·
        refine ⟨912309458885440239190369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1216412611847253652253825 912309458885440239190369)
        ·
          refine ⟨684232094164080179392777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 912309458885440239190369 684232094164080179392777)
          ·
            refine ⟨513174070623060134544583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 684232094164080179392777 513174070623060134544583)
            ·
              refine ⟨769761105934590201816875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513174070623060134544583 769761105934590201816875)
              ·
                refine ⟨1154641658901885302725313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769761105934590201816875 1154641658901885302725313)
                ·
                  refine ⟨865981244176413977043985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1154641658901885302725313 865981244176413977043985)
                  ·
                    refine ⟨649485933132310482782989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 865981244176413977043985 649485933132310482782989)
                    ·
                      refine ⟨243557224924616431043621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 649485933132310482782989 243557224924616431043621)
                      ·
                        rfl

theorem cell23_474326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_474326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474326 prefixEnd_474326 := by exact prefixLift 474326
  have htrace : WordTrace (prefixWord ++ tailWord_474326) baseStart_474326 baseEnd_474326 := by
    simpa [prefixWord, tailWord_474326, baseEnd_474326] using wordTrace_append hprefix tailTrace_474326
  have hstable : (prefixWord ++ tailWord_474326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474326).length < 2 ^ (prefixWord ++ tailWord_474326).sum := by decide
  have hdescent : baseEnd_474326 < baseStart_474326 := by decide
  rcases family_descends (prefixWord ++ tailWord_474326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474355 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 4, 4]
def baseStart_474355 : Nat := 118140960795 + 474355 * 2 ^ 59
def prefixEnd_474355 : Nat := 4983230072969 + 3 ^ 40 * 474355 * 2
def baseEnd_474355 : Nat := 81190705287865605860329

theorem tailTrace_474355 : CollatzResearch.WordTrace tailWord_474355 prefixEnd_474355 81190705287865605860329 := by
  unfold tailWord_474355
  simp only [CollatzResearch.WordTrace]
  refine ⟨17301148196500323229304519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11534098797666882152869679 17301148196500323229304519)
  ·
    refine ⟨25951722294750484843956779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17301148196500323229304519 25951722294750484843956779)
    ·
      refine ⟨38927583442125727265935169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25951722294750484843956779 38927583442125727265935169)
      ·
        refine ⟨29195687581594295449451377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38927583442125727265935169 29195687581594295449451377)
        ·
          refine ⟨21896765686195721587088533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29195687581594295449451377 21896765686195721587088533)
          ·
            refine ⟨1026410891540424449394775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21896765686195721587088533 1026410891540424449394775)
            ·
              refine ⟨1539616337310636674092163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026410891540424449394775 1539616337310636674092163)
              ·
                refine ⟨2309424505965955011138245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539616337310636674092163 2309424505965955011138245)
                ·
                  refine ⟨433017094868616564588421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2309424505965955011138245 433017094868616564588421)
                  ·
                    refine ⟨81190705287865605860329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 433017094868616564588421 81190705287865605860329)
                    ·
                      rfl

theorem cell23_474355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 4].length) (baseStart_474355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474355 prefixEnd_474355 := by exact prefixLift 474355
  have htrace : WordTrace (prefixWord ++ tailWord_474355) baseStart_474355 baseEnd_474355 := by
    simpa [prefixWord, tailWord_474355, baseEnd_474355] using wordTrace_append hprefix tailTrace_474355
  have hstable : (prefixWord ++ tailWord_474355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474355).length < 2 ^ (prefixWord ++ tailWord_474355).sum := by decide
  have hdescent : baseEnd_474355 < baseStart_474355 := by decide
  rcases family_descends (prefixWord ++ tailWord_474355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474372 : List Nat := [2, 3, 2, 2, 2, 3, 1, 1, 1, 6]
def baseStart_474372 : Nat := 118140960795 + 474372 * 2 ^ 59
def prefixEnd_474372 : Nat := 4983230072969 + 3 ^ 40 * 474372 * 2
def baseEnd_474372 : Nat := 81193615011574417022803

theorem tailTrace_474372 : CollatzResearch.WordTrace tailWord_474372 prefixEnd_474372 81193615011574417022803 := by
  unfold tailWord_474372
  simp only [CollatzResearch.WordTrace]
  refine ⟨8650884118719367566336685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11534512158292490088448913 8650884118719367566336685)
  ·
    refine ⟨3244081544519762837376257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8650884118719367566336685 3244081544519762837376257)
    ·
      refine ⟨2433061158389822128032193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3244081544519762837376257 2433061158389822128032193)
      ·
        refine ⟨1824795868792366596024145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2433061158389822128032193 1824795868792366596024145)
        ·
          refine ⟨1368596901594274947018109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1824795868792366596024145 1368596901594274947018109)
          ·
            refine ⟨513223838097853105131791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1368596901594274947018109 513223838097853105131791)
            ·
              refine ⟨769835757146779657697687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513223838097853105131791 769835757146779657697687)
              ·
                refine ⟨1154753635720169486546531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769835757146779657697687 1154753635720169486546531)
                ·
                  refine ⟨1732130453580254229819797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1154753635720169486546531 1732130453580254229819797)
                  ·
                    refine ⟨81193615011574417022803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1732130453580254229819797 81193615011574417022803)
                    ·
                      rfl

theorem cell23_474372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_474372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474372 prefixEnd_474372 := by exact prefixLift 474372
  have htrace : WordTrace (prefixWord ++ tailWord_474372) baseStart_474372 baseEnd_474372 := by
    simpa [prefixWord, tailWord_474372, baseEnd_474372] using wordTrace_append hprefix tailTrace_474372
  have hstable : (prefixWord ++ tailWord_474372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474372).length < 2 ^ (prefixWord ++ tailWord_474372).sum := by decide
  have hdescent : baseEnd_474372 < baseStart_474372 := by decide
  rcases family_descends (prefixWord ++ tailWord_474372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474382 : List Nat := [4, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3]
def baseStart_474382 : Nat := 118140960795 + 474382 * 2 ^ 59
def prefixEnd_474382 : Nat := 4983230072969 + 3 ^ 40 * 474382 * 2
def baseEnd_474382 : Nat := 243585979841268211943363

theorem tailTrace_474382 : CollatzResearch.WordTrace tailWord_474382 prefixEnd_474382 243585979841268211943363 := by
  unfold tailWord_474382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2162766620925313355067175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11534755311601671227024933 2162766620925313355067175)
  ·
    refine ⟨3244149931387970032600763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2162766620925313355067175 3244149931387970032600763)
    ·
      refine ⟨4866224897081955048901145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3244149931387970032600763 4866224897081955048901145)
      ·
        refine ⟨3649668672811466286675859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4866224897081955048901145 3649668672811466286675859)
        ·
          refine ⟨5474503009217199430013789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3649668672811466286675859 5474503009217199430013789)
          ·
            refine ⟨2052938628456449786255171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5474503009217199430013789 2052938628456449786255171)
            ·
              refine ⟨3079407942684674679382757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2052938628456449786255171 3079407942684674679382757)
              ·
                refine ⟨577388989253376502384267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3079407942684674679382757 577388989253376502384267)
                ·
                  refine ⟨866083483880064753576401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577388989253376502384267 866083483880064753576401)
                  ·
                    refine ⟨649562612910048565182301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 866083483880064753576401 649562612910048565182301)
                    ·
                      refine ⟨243585979841268211943363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 649562612910048565182301 243585979841268211943363)
                      ·
                        rfl

theorem cell23_474382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_474382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474382 prefixEnd_474382 := by exact prefixLift 474382
  have htrace : WordTrace (prefixWord ++ tailWord_474382) baseStart_474382 baseEnd_474382 := by
    simpa [prefixWord, tailWord_474382, baseEnd_474382] using wordTrace_append hprefix tailTrace_474382
  have hstable : (prefixWord ++ tailWord_474382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474382).length < 2 ^ (prefixWord ++ tailWord_474382).sum := by decide
  have hdescent : baseEnd_474382 < baseStart_474382 := by decide
  rcases family_descends (prefixWord ++ tailWord_474382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474396 : List Nat := [2, 2, 3, 1, 1, 1, 5, 3, 1, 2, 2]
def baseStart_474396 : Nat := 118140960795 + 474396 * 2 ^ 59
def prefixEnd_474396 : Nat := 4983230072969 + 3 ^ 40 * 474396 * 2
def baseEnd_474396 : Nat := 243593168570431157168299

theorem tailTrace_474396 : CollatzResearch.WordTrace tailWord_474396 prefixEnd_474396 243593168570431157168299 := by
  unfold tailWord_474396
  simp only [CollatzResearch.WordTrace]
  refine ⟨8651321794675893615773521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11535095726234524821031361 8651321794675893615773521)
  ·
    refine ⟨6488491346006920211830141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8651321794675893615773521 6488491346006920211830141)
    ·
      refine ⟨2433184254752595079436303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6488491346006920211830141 2433184254752595079436303)
      ·
        refine ⟨3649776382128892619154455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2433184254752595079436303 3649776382128892619154455)
        ·
          refine ⟨5474664573193338928731683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3649776382128892619154455 5474664573193338928731683)
          ·
            refine ⟨8211996859790008393097525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5474664573193338928731683 8211996859790008393097525)
            ·
              refine ⟨769874705605313286852893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8211996859790008393097525 769874705605313286852893)
              ·
                refine ⟨288703014601992482569835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 769874705605313286852893 288703014601992482569835)
                ·
                  refine ⟨433054521902988723854753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288703014601992482569835 433054521902988723854753)
                  ·
                    refine ⟨324790891427241542891065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 433054521902988723854753 324790891427241542891065)
                    ·
                      refine ⟨243593168570431157168299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 324790891427241542891065 243593168570431157168299)
                      ·
                        rfl

theorem cell23_474396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_474396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474396 prefixEnd_474396 := by exact prefixLift 474396
  have htrace : WordTrace (prefixWord ++ tailWord_474396) baseStart_474396 baseEnd_474396 := by
    simpa [prefixWord, tailWord_474396, baseEnd_474396] using wordTrace_append hprefix tailTrace_474396
  have hstable : (prefixWord ++ tailWord_474396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474396).length < 2 ^ (prefixWord ++ tailWord_474396).sum := by decide
  have hdescent : baseEnd_474396 < baseStart_474396 := by decide
  rcases family_descends (prefixWord ++ tailWord_474396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474402 : List Nat := [3, 3, 1, 1, 5, 1, 9]
def baseStart_474402 : Nat := 118140960795 + 474402 * 2 ^ 59
def prefixEnd_474402 : Nat := 4983230072969 + 3 ^ 40 * 474402 * 2
def baseEnd_474402 : Nat := 3007361104374791773991

theorem tailTrace_474402 : CollatzResearch.WordTrace tailWord_474402 prefixEnd_474402 3007361104374791773991 := by
  unfold tailWord_474402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4325715606832512564066365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11535241618220033504176973 4325715606832512564066365)
  ·
    refine ⟨1622143352562192211524887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4325715606832512564066365 1622143352562192211524887)
    ·
      refine ⟨2433215028843288317287331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1622143352562192211524887 2433215028843288317287331)
      ·
        refine ⟨3649822543264932475930997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2433215028843288317287331 3649822543264932475930997)
        ·
          refine ⟨342170863431087419618531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3649822543264932475930997 342170863431087419618531)
          ·
            refine ⟨513256295146631129427797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342170863431087419618531 513256295146631129427797)
            ·
              refine ⟨3007361104374791773991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 513256295146631129427797 3007361104374791773991)
              ·
                rfl

theorem cell23_474402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 9].length) (baseStart_474402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474402 prefixEnd_474402 := by exact prefixLift 474402
  have htrace : WordTrace (prefixWord ++ tailWord_474402) baseStart_474402 baseEnd_474402 := by
    simpa [prefixWord, tailWord_474402, baseEnd_474402] using wordTrace_append hprefix tailTrace_474402
  have hstable : (prefixWord ++ tailWord_474402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474402).length < 2 ^ (prefixWord ++ tailWord_474402).sum := by decide
  have hdescent : baseEnd_474402 < baseStart_474402 := by decide
  rcases family_descends (prefixWord ++ tailWord_474402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474412 : List Nat := [2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 3]
def baseStart_474412 : Nat := 118140960795 + 474412 * 2 ^ 59
def prefixEnd_474412 : Nat := 4983230072969 + 3 ^ 40 * 474412 * 2
def baseEnd_474412 : Nat := 243601384260903094568225

theorem tailTrace_474412 : CollatzResearch.WordTrace tailWord_474412 prefixEnd_474412 243601384260903094568225 := by
  unfold tailWord_474412
  simp only [CollatzResearch.WordTrace]
  refine ⟨8651613578646910982064745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11535484771529214642752993 8651613578646910982064745)
  ·
    refine ⟨6488710183985183236548559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8651613578646910982064745 6488710183985183236548559)
    ·
      refine ⟨9733065275977774854822839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6488710183985183236548559 9733065275977774854822839)
      ·
        refine ⟨14599597913966662282234259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9733065275977774854822839 14599597913966662282234259)
        ·
          refine ⟨21899396870949993423351389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14599597913966662282234259 21899396870949993423351389)
          ·
            refine ⟨8212273826606247533756771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21899396870949993423351389 8212273826606247533756771)
            ·
              refine ⟨12318410739909371300635157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8212273826606247533756771 12318410739909371300635157)
              ·
                refine ⟨577425503433251779717273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12318410739909371300635157 577425503433251779717273)
                ·
                  refine ⟨433069127574938834787955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577425503433251779717273 433069127574938834787955)
                  ·
                    refine ⟨649603691362408252181933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 433069127574938834787955 649603691362408252181933)
                    ·
                      refine ⟨243601384260903094568225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 649603691362408252181933 243601384260903094568225)
                      ·
                        rfl

theorem cell23_474412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 3].length) (baseStart_474412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474412 prefixEnd_474412 := by exact prefixLift 474412
  have htrace : WordTrace (prefixWord ++ tailWord_474412) baseStart_474412 baseEnd_474412 := by
    simpa [prefixWord, tailWord_474412, baseEnd_474412] using wordTrace_append hprefix tailTrace_474412
  have hstable : (prefixWord ++ tailWord_474412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474412).length < 2 ^ (prefixWord ++ tailWord_474412).sum := by decide
  have hdescent : baseEnd_474412 < baseStart_474412 := by decide
  rcases family_descends (prefixWord ++ tailWord_474412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474413 : List Nat := [1, 5, 3, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_474413 : Nat := 118140960795 + 474413 * 2 ^ 59
def prefixEnd_474413 : Nat := 4983230072969 + 3 ^ 40 * 474413 * 2
def baseEnd_474413 : Nat := 243601897741557590655721

theorem tailTrace_474413 : CollatzResearch.WordTrace tailWord_474413 prefixEnd_474413 243601897741557590655721 := by
  unfold tailWord_474413
  simp only [CollatzResearch.WordTrace]
  refine ⟨17303263630290199134915893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11535509086860132756610595 17303263630290199134915893)
  ·
    refine ⟨1622180965339706168898365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17303263630290199134915893 1622180965339706168898365)
    ·
      refine ⟨608317862002389813336887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1622180965339706168898365 608317862002389813336887)
      ·
        refine ⟨912476793003584720005331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608317862002389813336887 912476793003584720005331)
        ·
          refine ⟨1368715189505377080007997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912476793003584720005331 1368715189505377080007997)
          ·
            refine ⟨513268196064516405002999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1368715189505377080007997 513268196064516405002999)
            ·
              refine ⟨769902294096774607504499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513268196064516405002999 769902294096774607504499)
              ·
                refine ⟨1154853441145161911256749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769902294096774607504499 1154853441145161911256749)
                ·
                  refine ⟨433070040429435716721281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1154853441145161911256749 433070040429435716721281)
                  ·
                    refine ⟨324802530322076787540961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 433070040429435716721281 324802530322076787540961)
                    ·
                      refine ⟨243601897741557590655721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 324802530322076787540961 243601897741557590655721)
                      ·
                        rfl

theorem cell23_474413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_474413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474413 prefixEnd_474413 := by exact prefixLift 474413
  have htrace : WordTrace (prefixWord ++ tailWord_474413) baseStart_474413 baseEnd_474413 := by
    simpa [prefixWord, tailWord_474413, baseEnd_474413] using wordTrace_append hprefix tailTrace_474413
  have hstable : (prefixWord ++ tailWord_474413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474413).length < 2 ^ (prefixWord ++ tailWord_474413).sum := by decide
  have hdescent : baseEnd_474413 < baseStart_474413 := by decide
  rcases family_descends (prefixWord ++ tailWord_474413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474439 : List Nat := [1, 1, 4, 1, 2, 3, 3, 2, 1, 3, 2]
def baseStart_474439 : Nat := 118140960795 + 474439 * 2 ^ 59
def prefixEnd_474439 : Nat := 4983230072969 + 3 ^ 40 * 474439 * 2
def baseEnd_474439 : Nat := 243615248238574488930601

theorem tailTrace_474439 : CollatzResearch.WordTrace tailWord_474439 prefixEnd_474439 243615248238574488930601 := by
  unfold tailWord_474439
  simp only [CollatzResearch.WordTrace]
  refine ⟨17304211928196005575362371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11536141285464003716908247 17304211928196005575362371)
  ·
    refine ⟨25956317892294008363043557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17304211928196005575362371 25956317892294008363043557)
    ·
      refine ⟨4866809604805126568070667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25956317892294008363043557 4866809604805126568070667)
      ·
        refine ⟨7300214407207689852106001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4866809604805126568070667 7300214407207689852106001)
        ·
          refine ⟨5475160805405767389079501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7300214407207689852106001 5475160805405767389079501)
          ·
            refine ⟨2053185302027162770904813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5475160805405767389079501 2053185302027162770904813)
            ·
              refine ⟨769944488260186039089305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2053185302027162770904813 769944488260186039089305)
              ·
                refine ⟨577458366195139529316979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 769944488260186039089305 577458366195139529316979)
                ·
                  refine ⟨866187549292709293975469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577458366195139529316979 866187549292709293975469)
                  ·
                    refine ⟨324820330984765985240801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 866187549292709293975469 324820330984765985240801)
                    ·
                      refine ⟨243615248238574488930601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 324820330984765985240801 243615248238574488930601)
                      ·
                        rfl

theorem cell23_474439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_474439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474439 prefixEnd_474439 := by exact prefixLift 474439
  have htrace : WordTrace (prefixWord ++ tailWord_474439) baseStart_474439 baseEnd_474439 := by
    simpa [prefixWord, tailWord_474439, baseEnd_474439] using wordTrace_append hprefix tailTrace_474439
  have hstable : (prefixWord ++ tailWord_474439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474439).length < 2 ^ (prefixWord ++ tailWord_474439).sum := by decide
  have hdescent : baseEnd_474439 < baseStart_474439 := by decide
  rcases family_descends (prefixWord ++ tailWord_474439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474455 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 5]
def baseStart_474455 : Nat := 118140960795 + 474455 * 2 ^ 59
def prefixEnd_474455 : Nat := 4983230072969 + 3 ^ 40 * 474455 * 2
def baseEnd_474455 : Nat := 243623463929046426330527

theorem tailTrace_474455 : CollatzResearch.WordTrace tailWord_474455 prefixEnd_474455 243623463929046426330527 := by
  unfold tailWord_474455
  simp only [CollatzResearch.WordTrace]
  refine ⟨17304795496138040307944819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11536530330758693538629879 17304795496138040307944819)
  ·
    refine ⟨25957193244207060461917229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17304795496138040307944819 25957193244207060461917229)
    ·
      refine ⟨9733947466577647673218961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25957193244207060461917229 9733947466577647673218961)
      ·
        refine ⟨7300460599933235754914221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9733947466577647673218961 7300460599933235754914221)
        ·
          refine ⟨2737672724974963408092833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7300460599933235754914221 2737672724974963408092833)
          ·
            refine ⟨2053254543731222556069625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2737672724974963408092833 2053254543731222556069625)
            ·
              refine ⟨1539940907798416917052219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2053254543731222556069625 1539940907798416917052219)
              ·
                refine ⟨2309911361697625375578329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539940907798416917052219 2309911361697625375578329)
                ·
                  refine ⟨1732433521273219031683747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2309911361697625375578329 1732433521273219031683747)
                  ·
                    refine ⟨2598650281909828547525621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1732433521273219031683747 2598650281909828547525621)
                    ·
                      refine ⟨243623463929046426330527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2598650281909828547525621 243623463929046426330527)
                      ·
                        rfl

theorem cell23_474455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_474455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474455 prefixEnd_474455 := by exact prefixLift 474455
  have htrace : WordTrace (prefixWord ++ tailWord_474455) baseStart_474455 baseEnd_474455 := by
    simpa [prefixWord, tailWord_474455, baseEnd_474455] using wordTrace_append hprefix tailTrace_474455
  have hstable : (prefixWord ++ tailWord_474455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474455).length < 2 ^ (prefixWord ++ tailWord_474455).sum := by decide
  have hdescent : baseEnd_474455 < baseStart_474455 := by decide
  rcases family_descends (prefixWord ++ tailWord_474455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474520 : List Nat := [2, 1, 2, 5, 3, 1, 1, 2, 2, 2, 2]
def baseStart_474520 : Nat := 118140960795 + 474520 * 2 ^ 59
def prefixEnd_474520 : Nat := 4983230072969 + 3 ^ 40 * 474520 * 2
def baseEnd_474520 : Nat := 243656840171588672017729

theorem tailTrace_474520 : CollatzResearch.WordTrace tailWord_474520 prefixEnd_474520 243656840171588672017729 := by
  unfold tailWord_474520
  simp only [CollatzResearch.WordTrace]
  refine ⟨8653583120451278204530507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11538110827268370939374009 8653583120451278204530507)
  ·
    refine ⟨12980374680676917306795761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8653583120451278204530507 12980374680676917306795761)
    ·
      refine ⟨9735281010507687980096821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12980374680676917306795761 9735281010507687980096821)
      ·
        refine ⟨912682594735095748134077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9735281010507687980096821 912682594735095748134077)
        ·
          refine ⟨342255973025660905550279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 912682594735095748134077 342255973025660905550279)
          ·
            refine ⟨513383959538491358325419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342255973025660905550279 513383959538491358325419)
            ·
              refine ⟨770075939307737037488129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513383959538491358325419 770075939307737037488129)
              ·
                refine ⟨577556954480802778116097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 770075939307737037488129 577556954480802778116097)
                ·
                  refine ⟨433167715860602083587073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577556954480802778116097 433167715860602083587073)
                  ·
                    refine ⟨324875786895451562690305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 433167715860602083587073 324875786895451562690305)
                    ·
                      refine ⟨243656840171588672017729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 324875786895451562690305 243656840171588672017729)
                      ·
                        rfl

theorem cell23_474520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_474520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474520 prefixEnd_474520 := by exact prefixLift 474520
  have htrace : WordTrace (prefixWord ++ tailWord_474520) baseStart_474520 baseEnd_474520 := by
    simpa [prefixWord, tailWord_474520, baseEnd_474520] using wordTrace_append hprefix tailTrace_474520
  have hstable : (prefixWord ++ tailWord_474520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474520).length < 2 ^ (prefixWord ++ tailWord_474520).sum := by decide
  have hdescent : baseEnd_474520 < baseStart_474520 := by decide
  rcases family_descends (prefixWord ++ tailWord_474520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474552 : List Nat := [2, 1, 2, 1, 2, 2, 4, 2, 3, 4]
def baseStart_474552 : Nat := 118140960795 + 474552 * 2 ^ 59
def prefixEnd_474552 : Nat := 4983230072969 + 3 ^ 40 * 474552 * 2
def baseEnd_474552 : Nat := 81224423850844182272527

theorem tailTrace_474552 : CollatzResearch.WordTrace tailWord_474552 prefixEnd_474552 81224423850844182272527 := by
  unfold tailWord_474552
  simp only [CollatzResearch.WordTrace]
  refine ⟨8654166688393312937112955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11538888917857750582817273 8654166688393312937112955)
  ·
    refine ⟨12981250032589969405669433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8654166688393312937112955 12981250032589969405669433)
    ·
      refine ⟨9735937524442477054252075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12981250032589969405669433 9735937524442477054252075)
      ·
        refine ⟨14603906286663715581378113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9735937524442477054252075 14603906286663715581378113)
        ·
          refine ⟨10952929714997786686033585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14603906286663715581378113 10952929714997786686033585)
          ·
            refine ⟨8214697286248340014525189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10952929714997786686033585 8214697286248340014525189)
            ·
              refine ⟨1540255741171563752723473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8214697286248340014525189 1540255741171563752723473)
              ·
                refine ⟨1155191805878672814542605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1540255741171563752723473 1155191805878672814542605)
                ·
                  refine ⟨433196927204502305453477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1155191805878672814542605 433196927204502305453477)
                  ·
                    refine ⟨81224423850844182272527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 433196927204502305453477 81224423850844182272527)
                    ·
                      rfl

theorem cell23_474552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_474552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474552 prefixEnd_474552 := by exact prefixLift 474552
  have htrace : WordTrace (prefixWord ++ tailWord_474552) baseStart_474552 baseEnd_474552 := by
    simpa [prefixWord, tailWord_474552, baseEnd_474552] using wordTrace_append hprefix tailTrace_474552
  have hstable : (prefixWord ++ tailWord_474552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474552).length < 2 ^ (prefixWord ++ tailWord_474552).sum := by decide
  have hdescent : baseEnd_474552 < baseStart_474552 := by decide
  rcases family_descends (prefixWord ++ tailWord_474552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474599 : List Nat := [1, 1, 5, 2, 1, 2, 4, 1, 6]
def baseStart_474599 : Nat := 118140960795 + 474599 * 2 ^ 59
def prefixEnd_474599 : Nat := 4983230072969 + 3 ^ 40 * 474599 * 2
def baseEnd_474599 : Nat := 27077489460365984769985

theorem tailTrace_474599 : CollatzResearch.WordTrace tailWord_474599 prefixEnd_474599 27077489460365984769985 := by
  unfold tailWord_474599
  simp only [CollatzResearch.WordTrace]
  refine ⟨17310047607616352901186851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11540031738410901934124567 17310047607616352901186851)
  ·
    refine ⟨25965071411424529351780277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17310047607616352901186851 25965071411424529351780277)
    ·
      refine ⟨2434225444821049626729401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25965071411424529351780277 2434225444821049626729401)
      ·
        refine ⟨1825669083615787220047051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2434225444821049626729401 1825669083615787220047051)
        ·
          refine ⟨2738503625423680830070577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1825669083615787220047051 2738503625423680830070577)
          ·
            refine ⟨2053877719067760622552933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2738503625423680830070577 2053877719067760622552933)
            ·
              refine ⟨385102072325205116728675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2053877719067760622552933 385102072325205116728675)
              ·
                refine ⟨577653108487807675093013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385102072325205116728675 577653108487807675093013)
                ·
                  refine ⟨27077489460365984769985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 577653108487807675093013 27077489460365984769985)
                  ·
                    rfl

theorem cell23_474599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 6].length) (baseStart_474599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474599 prefixEnd_474599 := by exact prefixLift 474599
  have htrace : WordTrace (prefixWord ++ tailWord_474599) baseStart_474599 baseEnd_474599 := by
    simpa [prefixWord, tailWord_474599, baseEnd_474599] using wordTrace_append hprefix tailTrace_474599
  have hstable : (prefixWord ++ tailWord_474599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474599).length < 2 ^ (prefixWord ++ tailWord_474599).sum := by decide
  have hdescent : baseEnd_474599 < baseStart_474599 := by decide
  rcases family_descends (prefixWord ++ tailWord_474599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474643 : List Nat := [1, 1, 1, 2, 1, 6, 4, 2, 1, 1, 3]
def baseStart_474643 : Nat := 118140960795 + 474643 * 2 ^ 59
def prefixEnd_474643 : Nat := 4983230072969 + 3 ^ 40 * 474643 * 2
def baseEnd_474643 : Nat := 243719998292091690779663

theorem tailTrace_474643 : CollatzResearch.WordTrace tailWord_474643 prefixEnd_474643 243719998292091690779663 := by
  unfold tailWord_474643
  simp only [CollatzResearch.WordTrace]
  refine ⟨17311652419456948415788583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11541101612971298943859055 17311652419456948415788583)
  ·
    refine ⟨25967478629185422623682875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17311652419456948415788583 25967478629185422623682875)
    ·
      refine ⟨38951217943778133935524313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25967478629185422623682875 38951217943778133935524313)
      ·
        refine ⟨29213413457833600451643235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38951217943778133935524313 29213413457833600451643235)
        ·
          refine ⟨43820120186750400677464853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29213413457833600451643235 43820120186750400677464853)
          ·
            refine ⟨2054068133753925031756165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43820120186750400677464853 2054068133753925031756165)
            ·
              refine ⟨385137775078860943454281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2054068133753925031756165 385137775078860943454281)
              ·
                refine ⟨288853331309145707590711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385137775078860943454281 288853331309145707590711)
                ·
                  refine ⟨433279996963718561386067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288853331309145707590711 433279996963718561386067)
                  ·
                    refine ⟨649919995445577842079101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 433279996963718561386067 649919995445577842079101)
                    ·
                      refine ⟨243719998292091690779663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 649919995445577842079101 243719998292091690779663)
                      ·
                        rfl

theorem cell23_474643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 1, 1, 3].length) (baseStart_474643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474643 prefixEnd_474643 := by exact prefixLift 474643
  have htrace : WordTrace (prefixWord ++ tailWord_474643) baseStart_474643 baseEnd_474643 := by
    simpa [prefixWord, tailWord_474643, baseEnd_474643] using wordTrace_append hprefix tailTrace_474643
  have hstable : (prefixWord ++ tailWord_474643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474643).length < 2 ^ (prefixWord ++ tailWord_474643).sum := by decide
  have hdescent : baseEnd_474643 < baseStart_474643 := by decide
  rcases family_descends (prefixWord ++ tailWord_474643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474652 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_474652 : Nat := 118140960795 + 474652 * 2 ^ 59
def prefixEnd_474652 : Nat := 4983230072969 + 3 ^ 40 * 474652 * 2
def baseEnd_474652 : Nat := 243724619617982155567121

theorem tailTrace_474652 : CollatzResearch.WordTrace tailWord_474652 prefixEnd_474652 243724619617982155567121 := by
  unfold tailWord_474652
  simp only [CollatzResearch.WordTrace]
  refine ⟨8655990338212171476433105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11541320450949561968577473 8655990338212171476433105)
  ·
    refine ⟨6491992753659128607324829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8655990338212171476433105 6491992753659128607324829)
    ·
      refine ⟨2434497282622173227746811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6491992753659128607324829 2434497282622173227746811)
      ·
        refine ⟨3651745923933259841620217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2434497282622173227746811 3651745923933259841620217)
        ·
          refine ⟨2738809442949944881215163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3651745923933259841620217 2738809442949944881215163)
          ·
            refine ⟨4108214164424917321822745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2738809442949944881215163 4108214164424917321822745)
            ·
              refine ⟨3081160623318687991367059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4108214164424917321822745 3081160623318687991367059)
              ·
                refine ⟨4621740934978031987050589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3081160623318687991367059 4621740934978031987050589)
                ·
                  refine ⟨1733152850616761995143971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4621740934978031987050589 1733152850616761995143971)
                  ·
                    refine ⟨2599729275925142992715957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1733152850616761995143971 2599729275925142992715957)
                    ·
                      refine ⟨243724619617982155567121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2599729275925142992715957 243724619617982155567121)
                      ·
                        rfl

theorem cell23_474652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_474652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474652 prefixEnd_474652 := by exact prefixLift 474652
  have htrace : WordTrace (prefixWord ++ tailWord_474652) baseStart_474652 baseEnd_474652 := by
    simpa [prefixWord, tailWord_474652, baseEnd_474652] using wordTrace_append hprefix tailTrace_474652
  have hstable : (prefixWord ++ tailWord_474652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474652).length < 2 ^ (prefixWord ++ tailWord_474652).sum := by decide
  have hdescent : baseEnd_474652 < baseStart_474652 := by decide
  rcases family_descends (prefixWord ++ tailWord_474652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474659 : List Nat := [1, 1, 1, 4, 5, 1, 2, 1, 1, 6]
def baseStart_474659 : Nat := 118140960795 + 474659 * 2 ^ 59
def prefixEnd_474659 : Nat := 4983230072969 + 3 ^ 40 * 474659 * 2
def baseEnd_474659 : Nat := 81242737994187876059863

theorem tailTrace_474659 : CollatzResearch.WordTrace tailWord_474659 prefixEnd_474659 81242737994187876059863 := by
  unfold tailWord_474659
  simp only [CollatzResearch.WordTrace]
  refine ⟨17312235987398983148371031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11541490658265988765580687 17312235987398983148371031)
  ·
    refine ⟨25968353981098474722556547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17312235987398983148371031 25968353981098474722556547)
    ·
      refine ⟨38952530971647712083834821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25968353981098474722556547 38952530971647712083834821)
      ·
        refine ⟨7303599557183946015719029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38952530971647712083834821 7303599557183946015719029)
        ·
          refine ⟨684712458485994938973659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7303599557183946015719029 684712458485994938973659)
          ·
            refine ⟨1027068687728992408460489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684712458485994938973659 1027068687728992408460489)
            ·
              refine ⟨770301515796744306345367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1027068687728992408460489 770301515796744306345367)
              ·
                refine ⟨1155452273695116459518051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 770301515796744306345367 1155452273695116459518051)
                ·
                  refine ⟨1733178410542674689277077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1155452273695116459518051 1733178410542674689277077)
                  ·
                    refine ⟨81242737994187876059863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1733178410542674689277077 81242737994187876059863)
                    ·
                      rfl

theorem cell23_474659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 6].length) (baseStart_474659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474659 prefixEnd_474659 := by exact prefixLift 474659
  have htrace : WordTrace (prefixWord ++ tailWord_474659) baseStart_474659 baseEnd_474659 := by
    simpa [prefixWord, tailWord_474659, baseEnd_474659] using wordTrace_append hprefix tailTrace_474659
  have hstable : (prefixWord ++ tailWord_474659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474659).length < 2 ^ (prefixWord ++ tailWord_474659).sum := by decide
  have hdescent : baseEnd_474659 < baseStart_474659 := by decide
  rcases family_descends (prefixWord ++ tailWord_474659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474710 : List Nat := [5, 2, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_474710 : Nat := 118140960795 + 474710 * 2 ^ 59
def prefixEnd_474710 : Nat := 4983230072969 + 3 ^ 40 * 474710 * 2
def baseEnd_474710 : Nat := 81251467165314309547285

theorem tailTrace_474710 : CollatzResearch.WordTrace tailWord_474710 prefixEnd_474710 81251467165314309547285 := by
  unfold tailWord_474710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1082131006888388678654849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11542730740142812572318389 1082131006888388678654849)
  ·
    refine ⟨811598255166291508991137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1082131006888388678654849 811598255166291508991137)
    ·
      refine ⟨608698691374718631743353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 811598255166291508991137 608698691374718631743353)
      ·
        refine ⟨456524018531038973807515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608698691374718631743353 456524018531038973807515)
        ·
          refine ⟨684786027796558460711273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456524018531038973807515 684786027796558460711273)
          ·
            refine ⟨513589520847418845533455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 684786027796558460711273 513589520847418845533455)
            ·
              refine ⟨770384281271128268300183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513589520847418845533455 770384281271128268300183)
              ·
                refine ⟨1155576421906692402450275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 770384281271128268300183 1155576421906692402450275)
                ·
                  refine ⟨1733364632860038603675413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1155576421906692402450275 1733364632860038603675413)
                  ·
                    refine ⟨81251467165314309547285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1733364632860038603675413 81251467165314309547285)
                    ·
                      rfl

theorem cell23_474710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_474710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474710 prefixEnd_474710 := by exact prefixLift 474710
  have htrace : WordTrace (prefixWord ++ tailWord_474710) baseStart_474710 baseEnd_474710 := by
    simpa [prefixWord, tailWord_474710, baseEnd_474710] using wordTrace_append hprefix tailTrace_474710
  have hstable : (prefixWord ++ tailWord_474710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474710).length < 2 ^ (prefixWord ++ tailWord_474710).sum := by decide
  have hdescent : baseEnd_474710 < baseStart_474710 := by decide
  rcases family_descends (prefixWord ++ tailWord_474710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474716 : List Nat := [2, 2, 4, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_474716 : Nat := 118140960795 + 474716 * 2 ^ 59
def prefixEnd_474716 : Nat := 4983230072969 + 3 ^ 40 * 474716 * 2
def baseEnd_474716 : Nat := 243757482379869905166827

theorem tailTrace_474716 : CollatzResearch.WordTrace tailWord_474716 prefixEnd_474716 243757482379869905166827 := by
  unfold tailWord_474716
  simp only [CollatzResearch.WordTrace]
  refine ⟨8657157474096240941598001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11542876632128321255464001 8657157474096240941598001)
  ·
    refine ⟨6492868105572180706198501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8657157474096240941598001 6492868105572180706198501)
    ·
      refine ⟨1217412769794783882412219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6492868105572180706198501 1217412769794783882412219)
      ·
        refine ⟨1826119154692175823618329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1217412769794783882412219 1826119154692175823618329)
        ·
          refine ⟨1369589366019131867713747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1826119154692175823618329 1369589366019131867713747)
          ·
            refine ⟨2054384049028697801570621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1369589366019131867713747 2054384049028697801570621)
            ·
              refine ⟨770394018385761675588983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2054384049028697801570621 770394018385761675588983)
              ·
                refine ⟨1155591027578642513383475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 770394018385761675588983 1155591027578642513383475)
                ·
                  refine ⟨1733386541367963770075213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1155591027578642513383475 1733386541367963770075213)
                  ·
                    refine ⟨650019953012986413778205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1733386541367963770075213 650019953012986413778205)
                    ·
                      refine ⟨243757482379869905166827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 650019953012986413778205 243757482379869905166827)
                      ·
                        rfl

theorem cell23_474716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_474716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474716 prefixEnd_474716 := by exact prefixLift 474716
  have htrace : WordTrace (prefixWord ++ tailWord_474716) baseStart_474716 baseEnd_474716 := by
    simpa [prefixWord, tailWord_474716, baseEnd_474716] using wordTrace_append hprefix tailTrace_474716
  have hstable : (prefixWord ++ tailWord_474716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474716).length < 2 ^ (prefixWord ++ tailWord_474716).sum := by decide
  have hdescent : baseEnd_474716 < baseStart_474716 := by decide
  rcases family_descends (prefixWord ++ tailWord_474716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474734 : List Nat := [4, 1, 2, 2, 4, 1, 1, 3, 1, 2, 2]
def baseStart_474734 : Nat := 118140960795 + 474734 * 2 ^ 59
def prefixEnd_474734 : Nat := 4983230072969 + 3 ^ 40 * 474734 * 2
def baseEnd_474734 : Nat := 243766725031650834741745

theorem tailTrace_474734 : CollatzResearch.WordTrace tailWord_474734 prefixEnd_474734 243766725031650834741745 := by
  unfold tailWord_474734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2164371432765908869668907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11543314308084847304900837 2164371432765908869668907)
  ·
    refine ⟨3246557149148863304503361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2164371432765908869668907 3246557149148863304503361)
    ·
      refine ⟨2434917861861647478377521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3246557149148863304503361 2434917861861647478377521)
      ·
        refine ⟨1826188396396235608783141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2434917861861647478377521 1826188396396235608783141)
        ·
          refine ⟨342410324324294176646839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1826188396396235608783141 342410324324294176646839)
          ·
            refine ⟨513615486486441264970259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342410324324294176646839 513615486486441264970259)
            ·
              refine ⟨770423229729661897455389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513615486486441264970259 770423229729661897455389)
              ·
                refine ⟨288908711148623211545771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 770423229729661897455389 288908711148623211545771)
                ·
                  refine ⟨433363066722934817318657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288908711148623211545771 433363066722934817318657)
                  ·
                    refine ⟨325022300042201112988993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 433363066722934817318657 325022300042201112988993)
                    ·
                      refine ⟨243766725031650834741745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 325022300042201112988993 243766725031650834741745)
                      ·
                        rfl

theorem cell23_474734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_474734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474734 prefixEnd_474734 := by exact prefixLift 474734
  have htrace : WordTrace (prefixWord ++ tailWord_474734) baseStart_474734 baseEnd_474734 := by
    simpa [prefixWord, tailWord_474734, baseEnd_474734] using wordTrace_append hprefix tailTrace_474734
  have hstable : (prefixWord ++ tailWord_474734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474734).length < 2 ^ (prefixWord ++ tailWord_474734).sum := by decide
  have hdescent : baseEnd_474734 < baseStart_474734 := by decide
  rcases family_descends (prefixWord ++ tailWord_474734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474809 : List Nat := [1, 2, 1, 4, 1, 1, 4, 2, 2, 5]
def baseStart_474809 : Nat := 118140960795 + 474809 * 2 ^ 59
def prefixEnd_474809 : Nat := 4983230072969 + 3 ^ 40 * 474809 * 2
def baseEnd_474809 : Nat := 81268412026912680434633

theorem tailTrace_474809 : CollatzResearch.WordTrace tailWord_474809 prefixEnd_474809 81268412026912680434633 := by
  unfold tailWord_474809
  simp only [CollatzResearch.WordTrace]
  refine ⟨17317706936855558766331481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11545137957903705844220987 17317706936855558766331481)
  ·
    refine ⟨12988280202641669074748611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17317706936855558766331481 12988280202641669074748611)
    ·
      refine ⟨19482420303962503612122917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12988280202641669074748611 19482420303962503612122917)
      ·
        refine ⟨3652953806992969427273047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19482420303962503612122917 3652953806992969427273047)
        ·
          refine ⟨5479430710489454140909571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3652953806992969427273047 5479430710489454140909571)
          ·
            refine ⟨8219146065734181211364357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5479430710489454140909571 8219146065734181211364357)
            ·
              refine ⟨1541089887325158977130817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8219146065734181211364357 1541089887325158977130817)
              ·
                refine ⟨1155817415493869232848113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1541089887325158977130817 1155817415493869232848113)
                ·
                  refine ⟨866863061620401924636085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1155817415493869232848113 866863061620401924636085)
                  ·
                    refine ⟨81268412026912680434633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 866863061620401924636085 81268412026912680434633)
                    ·
                      rfl

theorem cell23_474809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 5].length) (baseStart_474809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474809 prefixEnd_474809 := by exact prefixLift 474809
  have htrace : WordTrace (prefixWord ++ tailWord_474809) baseStart_474809 baseEnd_474809 := by
    simpa [prefixWord, tailWord_474809, baseEnd_474809] using wordTrace_append hprefix tailTrace_474809
  have hstable : (prefixWord ++ tailWord_474809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474809).length < 2 ^ (prefixWord ++ tailWord_474809).sum := by decide
  have hdescent : baseEnd_474809 < baseStart_474809 := by decide
  rcases family_descends (prefixWord ++ tailWord_474809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474866 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 4, 2, 3]
def baseStart_474866 : Nat := 118140960795 + 474866 * 2 ^ 59
def prefixEnd_474866 : Nat := 4983230072969 + 3 ^ 40 * 474866 * 2
def baseEnd_474866 : Nat := 243834504478044318291137

theorem tailTrace_474866 : CollatzResearch.WordTrace tailWord_474866 prefixEnd_474866 243834504478044318291137 := by
  unfold tailWord_474866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4329946474412264375289113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11546523931766038334104301 4329946474412264375289113)
  ·
    refine ⟨3247459855809198281466835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4329946474412264375289113 3247459855809198281466835)
    ·
      refine ⟨4871189783713797422200253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3247459855809198281466835 4871189783713797422200253)
      ·
        refine ⟨1826696168892674033325095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4871189783713797422200253 1826696168892674033325095)
        ·
          refine ⟨2740044253339011049987643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1826696168892674033325095 2740044253339011049987643)
          ·
            refine ⟨4110066380008516574981465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2740044253339011049987643 4110066380008516574981465)
            ·
              refine ⟨3082549785006387431236099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4110066380008516574981465 3082549785006387431236099)
              ·
                refine ⟨4623824677509581146854149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3082549785006387431236099 4623824677509581146854149)
                ·
                  refine ⟨866967127033046465035153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4623824677509581146854149 866967127033046465035153)
                  ·
                    refine ⟨650225345274784848776365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 866967127033046465035153 650225345274784848776365)
                    ·
                      refine ⟨243834504478044318291137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 650225345274784848776365 243834504478044318291137)
                      ·
                        rfl

theorem cell23_474866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_474866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474866 prefixEnd_474866 := by exact prefixLift 474866
  have htrace : WordTrace (prefixWord ++ tailWord_474866) baseStart_474866 baseEnd_474866 := by
    simpa [prefixWord, tailWord_474866, baseEnd_474866] using wordTrace_append hprefix tailTrace_474866
  have hstable : (prefixWord ++ tailWord_474866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474866).length < 2 ^ (prefixWord ++ tailWord_474866).sum := by decide
  have hdescent : baseEnd_474866 < baseStart_474866 := by decide
  rcases family_descends (prefixWord ++ tailWord_474866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474930 : List Nat := [3, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3]
def baseStart_474930 : Nat := 118140960795 + 474930 * 2 ^ 59
def prefixEnd_474930 : Nat := 4983230072969 + 3 ^ 40 * 474930 * 2
def baseEnd_474930 : Nat := 243867367239932067890843

theorem tailTrace_474930 : CollatzResearch.WordTrace tailWord_474930 prefixEnd_474930 243867367239932067890843 := by
  unfold tailWord_474930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4330530042354299107871561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11548080112944797620990829 4330530042354299107871561)
  ·
    refine ⟨3247897531765724330903671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4330530042354299107871561 3247897531765724330903671)
    ·
      refine ⟨4871846297648586496355507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3247897531765724330903671 4871846297648586496355507)
      ·
        refine ⟨7307769446472879744533261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4871846297648586496355507 7307769446472879744533261)
        ·
          refine ⟨2740413542427329904199973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7307769446472879744533261 2740413542427329904199973)
          ·
            refine ⟨513827539205124357037495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2740413542427329904199973 513827539205124357037495)
            ·
              refine ⟨770741308807686535556243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513827539205124357037495 770741308807686535556243)
              ·
                refine ⟨1156111963211529803334365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 770741308807686535556243 1156111963211529803334365)
                ·
                  refine ⟨433541986204323676250387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1156111963211529803334365 433541986204323676250387)
                  ·
                    refine ⟨650312979306485514375581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 433541986204323676250387 650312979306485514375581)
                    ·
                      refine ⟨243867367239932067890843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 650312979306485514375581 243867367239932067890843)
                      ·
                        rfl

theorem cell23_474930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_474930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474930 prefixEnd_474930 := by exact prefixLift 474930
  have htrace : WordTrace (prefixWord ++ tailWord_474930) baseStart_474930 baseEnd_474930 := by
    simpa [prefixWord, tailWord_474930, baseEnd_474930] using wordTrace_append hprefix tailTrace_474930
  have hstable : (prefixWord ++ tailWord_474930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474930).length < 2 ^ (prefixWord ++ tailWord_474930).sum := by decide
  have hdescent : baseEnd_474930 < baseStart_474930 := by decide
  rcases family_descends (prefixWord ++ tailWord_474930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474937 : List Nat := [1, 2, 1, 7, 2, 1, 2, 1, 6]
def baseStart_474937 : Nat := 118140960795 + 474937 * 2 ^ 59
def prefixEnd_474937 : Nat := 4983230072969 + 3 ^ 40 * 474937 * 2
def baseEnd_474937 : Nat := 27096773511612615611479

theorem tailTrace_474937 : CollatzResearch.WordTrace tailWord_474937 prefixEnd_474937 27096773511612615611479 := by
  unfold tailWord_474937
  simp only [CollatzResearch.WordTrace]
  refine ⟨17322375480391836626991065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11548250320261224417994043 17322375480391836626991065)
  ·
    refine ⟨12991781610293877470243299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17322375480391836626991065 12991781610293877470243299)
    ·
      refine ⟨19487672415440816205364949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12991781610293877470243299 19487672415440816205364949)
      ·
        refine ⟨456742322236894129813241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 19487672415440816205364949 456742322236894129813241)
        ·
          refine ⟨342556741677670597359931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456742322236894129813241 342556741677670597359931)
          ·
            refine ⟨513835112516505896039897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342556741677670597359931 513835112516505896039897)
            ·
              refine ⟨385376334387379422029923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513835112516505896039897 385376334387379422029923)
              ·
                refine ⟨578064501581069133044885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385376334387379422029923 578064501581069133044885)
                ·
                  refine ⟨27096773511612615611479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 578064501581069133044885 27096773511612615611479)
                  ·
                    rfl

theorem cell23_474937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 6].length) (baseStart_474937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474937 prefixEnd_474937 := by exact prefixLift 474937
  have htrace : WordTrace (prefixWord ++ tailWord_474937) baseStart_474937 baseEnd_474937 := by
    simpa [prefixWord, tailWord_474937, baseEnd_474937] using wordTrace_append hprefix tailTrace_474937
  have hstable : (prefixWord ++ tailWord_474937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474937).length < 2 ^ (prefixWord ++ tailWord_474937).sum := by decide
  have hdescent : baseEnd_474937 < baseStart_474937 := by decide
  rcases family_descends (prefixWord ++ tailWord_474937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474949 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 1, 1, 6]
def baseStart_474949 : Nat := 118140960795 + 474949 * 2 ^ 59
def prefixEnd_474949 : Nat := 4983230072969 + 3 ^ 40 * 474949 * 2
def baseEnd_474949 : Nat := 243877123372367493553255

theorem tailTrace_474949 : CollatzResearch.WordTrace tailWord_474949 prefixEnd_474949 243877123372367493553255 := by
  unfold tailWord_474949
  simp only [CollatzResearch.WordTrace]
  refine ⟨17322813156348362676427901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11548542104232241784285267 17322813156348362676427901)
  ·
    refine ⟨6496054933630636003660463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17322813156348362676427901 6496054933630636003660463)
    ·
      refine ⟨9744082400445954005490695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6496054933630636003660463 9744082400445954005490695)
      ·
        refine ⟨14616123600668931008236043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9744082400445954005490695 14616123600668931008236043)
        ·
          refine ⟨21924185401003396512354065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14616123600668931008236043 21924185401003396512354065)
          ·
            refine ⟨16443139050752547384265549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21924185401003396512354065 16443139050752547384265549)
            ·
              refine ⟨6166177144032205269099581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16443139050752547384265549 6166177144032205269099581)
              ·
                refine ⟨2312316429012076975912343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6166177144032205269099581 2312316429012076975912343)
                ·
                  refine ⟨3468474643518115463868515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2312316429012076975912343 3468474643518115463868515)
                  ·
                    refine ⟨5202711965277173195802773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3468474643518115463868515 5202711965277173195802773)
                    ·
                      refine ⟨243877123372367493553255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5202711965277173195802773 243877123372367493553255)
                      ·
                        rfl

theorem cell23_474949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_474949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474949 prefixEnd_474949 := by exact prefixLift 474949
  have htrace : WordTrace (prefixWord ++ tailWord_474949) baseStart_474949 baseEnd_474949 := by
    simpa [prefixWord, tailWord_474949, baseEnd_474949] using wordTrace_append hprefix tailTrace_474949
  have hstable : (prefixWord ++ tailWord_474949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474949).length < 2 ^ (prefixWord ++ tailWord_474949).sum := by decide
  have hdescent : baseEnd_474949 < baseStart_474949 := by decide
  rcases family_descends (prefixWord ++ tailWord_474949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474950 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_474950 : Nat := 118140960795 + 474950 * 2 ^ 59
def prefixEnd_474950 : Nat := 4983230072969 + 3 ^ 40 * 474950 * 2
def baseEnd_474950 : Nat := 81292545617673996546917

theorem tailTrace_474950 : CollatzResearch.WordTrace tailWord_474950 prefixEnd_474950 81292545617673996546917 := by
  unfold tailWord_474950
  simp only [CollatzResearch.WordTrace]
  refine ⟨541339050917023120225447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11548566419563159898142869 541339050917023120225447)
  ·
    refine ⟨812008576375534680338171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 541339050917023120225447 812008576375534680338171)
    ·
      refine ⟨1218012864563302020507257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 812008576375534680338171 1218012864563302020507257)
      ·
        refine ⟨913509648422476515380443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1218012864563302020507257 913509648422476515380443)
        ·
          refine ⟨1370264472633714773070665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913509648422476515380443 1370264472633714773070665)
          ·
            refine ⟨1027698354475286079802999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1370264472633714773070665 1027698354475286079802999)
            ·
              refine ⟨1541547531712929119704499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027698354475286079802999 1541547531712929119704499)
              ·
                refine ⟨2312321297569393679556749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541547531712929119704499 2312321297569393679556749)
                ·
                  refine ⟨867120486588522629833781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2312321297569393679556749 867120486588522629833781)
                  ·
                    refine ⟨81292545617673996546917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 867120486588522629833781 81292545617673996546917)
                    ·
                      rfl

theorem cell23_474950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_474950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474950 prefixEnd_474950 := by exact prefixLift 474950
  have htrace : WordTrace (prefixWord ++ tailWord_474950) baseStart_474950 baseEnd_474950 := by
    simpa [prefixWord, tailWord_474950, baseEnd_474950] using wordTrace_append hprefix tailTrace_474950
  have hstable : (prefixWord ++ tailWord_474950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474950).length < 2 ^ (prefixWord ++ tailWord_474950).sum := by decide
  have hdescent : baseEnd_474950 < baseStart_474950 := by decide
  rcases family_descends (prefixWord ++ tailWord_474950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
