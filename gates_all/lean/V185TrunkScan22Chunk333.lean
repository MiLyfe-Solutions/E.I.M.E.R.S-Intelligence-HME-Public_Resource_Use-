import V185TrunkScan22Chunk332

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2971348 : List Nat := [2, 4, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_2971348 : Nat := 118140960795 + 2971348 * 2 ^ 59
def prefixEnd_2971348 : Nat := 4983230072969 + 3 ^ 40 * 2971348 * 2
def baseEnd_2971348 : Nat := 1017153143850497213990017

theorem tailTrace_2971348 : CollatzResearch.WordTrace tailWord_2971348 prefixEnd_2971348 1017153143850497213990017 := by
  unfold tailWord_2971348
  simp only [CollatzResearch.WordTrace]
  refine ⟨54186982419660568341045349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72249309892880757788060465 54186982419660568341045349)
  ·
    refine ⟨10160059203686356563946003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54186982419660568341045349 10160059203686356563946003)
    ·
      refine ⟨15240088805529534845919005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10160059203686356563946003 15240088805529534845919005)
      ·
        refine ⟨5715033302073575567219627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15240088805529534845919005 5715033302073575567219627)
        ·
          refine ⟨8572549953110363350829441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5715033302073575567219627 8572549953110363350829441)
          ·
            refine ⟨6429412464832772513122081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8572549953110363350829441 6429412464832772513122081)
            ·
              refine ⟨4822059348624579384841561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6429412464832772513122081 4822059348624579384841561)
              ·
                refine ⟨3616544511468434538631171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4822059348624579384841561 3616544511468434538631171)
                ·
                  refine ⟨5424816767202651807946757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3616544511468434538631171 5424816767202651807946757)
                  ·
                    refine ⟨1017153143850497213990017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5424816767202651807946757 1017153143850497213990017)
                    ·
                      rfl

theorem cell22_2971348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_2971348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971348 prefixEnd_2971348 := by exact prefixLift 2971348
  have htrace : WordTrace (prefixWord ++ tailWord_2971348) baseStart_2971348 baseEnd_2971348 := by
    simpa [prefixWord, tailWord_2971348, baseEnd_2971348] using wordTrace_append hprefix tailTrace_2971348
  have hstable : (prefixWord ++ tailWord_2971348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971348).length < 2 ^ (prefixWord ++ tailWord_2971348).sum := by decide
  have hdescent : baseEnd_2971348 < baseStart_2971348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971359 : List Nat := [1, 1, 2, 3, 2, 2, 2, 3, 2, 4]
def baseStart_2971359 : Nat := 118140960795 + 2971359 * 2 ^ 59
def prefixEnd_2971359 : Nat := 4983230072969 + 3 ^ 40 * 2971359 * 2
def baseEnd_2971359 : Nat := 1017156909375296851964983

theorem tailTrace_2971359 : CollatzResearch.WordTrace tailWord_2971359 prefixEnd_2971359 1017156909375296851964983 := by
  unfold tailWord_2971359
  simp only [CollatzResearch.WordTrace]
  refine ⟨108374366042281285560741131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72249577361520857040494087 108374366042281285560741131)
  ·
    refine ⟨162561549063421928341111697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108374366042281285560741131 162561549063421928341111697)
    ·
      refine ⟨121921161797566446255833773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162561549063421928341111697 121921161797566446255833773)
      ·
        refine ⟨45720435674087417345937665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121921161797566446255833773 45720435674087417345937665)
        ·
          refine ⟨34290326755565563009453249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45720435674087417345937665 34290326755565563009453249)
          ·
            refine ⟨25717745066674172257089937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34290326755565563009453249 25717745066674172257089937)
            ·
              refine ⟨19288308800005629192817453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25717745066674172257089937 19288308800005629192817453)
              ·
                refine ⟨7233115800002110947306545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19288308800005629192817453 7233115800002110947306545)
                ·
                  refine ⟨5424836850001583210479909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7233115800002110947306545 5424836850001583210479909)
                  ·
                    refine ⟨1017156909375296851964983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5424836850001583210479909 1017156909375296851964983)
                    ·
                      rfl

theorem cell22_2971359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_2971359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971359 prefixEnd_2971359 := by exact prefixLift 2971359
  have htrace : WordTrace (prefixWord ++ tailWord_2971359) baseStart_2971359 baseEnd_2971359 := by
    simpa [prefixWord, tailWord_2971359, baseEnd_2971359] using wordTrace_append hprefix tailTrace_2971359
  have hstable : (prefixWord ++ tailWord_2971359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971359).length < 2 ^ (prefixWord ++ tailWord_2971359).sum := by decide
  have hdescent : baseEnd_2971359 < baseStart_2971359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971380 : List Nat := [2, 6, 1, 1, 1, 3, 1, 1, 6]
def baseStart_2971380 : Nat := 118140960795 + 2971380 * 2 ^ 59
def prefixEnd_2971380 : Nat := 4983230072969 + 3 ^ 40 * 2971380 * 2
def baseEnd_2971380 : Nat := 339054699368153265729973

theorem tailTrace_2971380 : CollatzResearch.WordTrace tailWord_2971380 prefixEnd_2971380 339054699368153265729973 := by
  unfold tailWord_2971380
  simp only [CollatzResearch.WordTrace]
  refine ⟨54187565987602603073627797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72250087983470137431503729 54187565987602603073627797)
  ·
    refine ⟨2540042155668872019076303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54187565987602603073627797 2540042155668872019076303)
    ·
      refine ⟨3810063233503308028614455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2540042155668872019076303 3810063233503308028614455)
      ·
        refine ⟨5715094850254962042921683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3810063233503308028614455 5715094850254962042921683)
        ·
          refine ⟨8572642275382443064382525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5715094850254962042921683 8572642275382443064382525)
          ·
            refine ⟨3214740853268416149143447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8572642275382443064382525 3214740853268416149143447)
            ·
              refine ⟨4822111279902624223715171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3214740853268416149143447 4822111279902624223715171)
              ·
                refine ⟨7233166919853936335572757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4822111279902624223715171 7233166919853936335572757)
                ·
                  refine ⟨339054699368153265729973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7233166919853936335572757 339054699368153265729973)
                  ·
                    rfl

theorem cell22_2971380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_2971380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971380 prefixEnd_2971380 := by exact prefixLift 2971380
  have htrace : WordTrace (prefixWord ++ tailWord_2971380) baseStart_2971380 baseEnd_2971380 := by
    simpa [prefixWord, tailWord_2971380, baseEnd_2971380] using wordTrace_append hprefix tailTrace_2971380
  have hstable : (prefixWord ++ tailWord_2971380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971380).length < 2 ^ (prefixWord ++ tailWord_2971380).sum := by decide
  have hdescent : baseEnd_2971380 < baseStart_2971380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971406 : List Nat := [4, 1, 1, 2, 1, 1, 2, 4, 3, 3]
def baseStart_2971406 : Nat := 118140960795 + 2971406 * 2 ^ 59
def prefixEnd_2971406 : Nat := 4983230072969 + 3 ^ 40 * 2971406 * 2
def baseEnd_2971406 : Nat := 1017172998435804396039839

theorem tailTrace_2971406 : CollatzResearch.WordTrace tailWord_2971406 prefixEnd_2971406 1017172998435804396039839 := by
  unfold tailWord_2971406
  simp only [CollatzResearch.WordTrace]
  refine ⟨13547010034138876573462759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72250720182074008391801381 13547010034138876573462759)
  ·
    refine ⟨20320515051208314860194139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13547010034138876573462759 20320515051208314860194139)
    ·
      refine ⟨30480772576812472290291209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20320515051208314860194139 30480772576812472290291209)
      ·
        refine ⟨22860579432609354217718407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30480772576812472290291209 22860579432609354217718407)
        ·
          refine ⟨34290869148914031326577611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22860579432609354217718407 34290869148914031326577611)
          ·
            refine ⟨51436303723371046989866417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34290869148914031326577611 51436303723371046989866417)
            ·
              refine ⟨38577227792528285242399813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51436303723371046989866417 38577227792528285242399813)
              ·
                refine ⟨7233230211099053482949965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38577227792528285242399813 7233230211099053482949965)
                ·
                  refine ⟨2712461329162145056106237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7233230211099053482949965 2712461329162145056106237)
                  ·
                    refine ⟨1017172998435804396039839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2712461329162145056106237 1017172998435804396039839)
                    ·
                      rfl

theorem cell22_2971406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_2971406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971406 prefixEnd_2971406 := by exact prefixLift 2971406
  have htrace : WordTrace (prefixWord ++ tailWord_2971406) baseStart_2971406 baseEnd_2971406 := by
    simpa [prefixWord, tailWord_2971406, baseEnd_2971406] using wordTrace_append hprefix tailTrace_2971406
  have hstable : (prefixWord ++ tailWord_2971406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971406).length < 2 ^ (prefixWord ++ tailWord_2971406).sum := by decide
  have hdescent : baseEnd_2971406 < baseStart_2971406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971423 : List Nat := [1, 1, 2, 4, 2, 1, 2, 5, 1, 3]
def baseStart_2971423 : Nat := 118140960795 + 2971423 * 2 ^ 59
def prefixEnd_2971423 : Nat := 4983230072969 + 3 ^ 40 * 2971423 * 2
def baseEnd_2971423 : Nat := 1017178817883222018364787

theorem tailTrace_2971423 : CollatzResearch.WordTrace tailWord_2971423 prefixEnd_2971423 1017178817883222018364787 := by
  unfold tailWord_2971423
  simp only [CollatzResearch.WordTrace]
  refine ⟨108376700314049424491070923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72251133542699616327380615 108376700314049424491070923)
  ·
    refine ⟨162565050471074136736606385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108376700314049424491070923 162565050471074136736606385)
    ·
      refine ⟨121923787853305602552454789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162565050471074136736606385 121923787853305602552454789)
      ·
        refine ⟨22860710222494800478585273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121923787853305602552454789 22860710222494800478585273)
        ·
          refine ⟨17145532666871100358938955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22860710222494800478585273 17145532666871100358938955)
          ·
            refine ⟨25718299000306650538408433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17145532666871100358938955 25718299000306650538408433)
            ·
              refine ⟨19288724250229987903806325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25718299000306650538408433 19288724250229987903806325)
              ·
                refine ⟨1808317898459061365981843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19288724250229987903806325 1808317898459061365981843)
                ·
                  refine ⟨2712476847688592048972765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1808317898459061365981843 2712476847688592048972765)
                  ·
                    refine ⟨1017178817883222018364787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2712476847688592048972765 1017178817883222018364787)
                    ·
                      rfl

theorem cell22_2971423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 1, 3].length) (baseStart_2971423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971423 prefixEnd_2971423 := by exact prefixLift 2971423
  have htrace : WordTrace (prefixWord ++ tailWord_2971423) baseStart_2971423 baseEnd_2971423 := by
    simpa [prefixWord, tailWord_2971423, baseEnd_2971423] using wordTrace_append hprefix tailTrace_2971423
  have hstable : (prefixWord ++ tailWord_2971423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971423).length < 2 ^ (prefixWord ++ tailWord_2971423).sum := by decide
  have hdescent : baseEnd_2971423 < baseStart_2971423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971436 : List Nat := [2, 2, 1, 1, 1, 6, 2, 2, 5]
def baseStart_2971436 : Nat := 118140960795 + 2971436 * 2 ^ 59
def prefixEnd_2971436 : Nat := 4983230072969 + 3 ^ 40 * 2971436 * 2
def baseEnd_2971436 : Nat := 339061089349631439263249

theorem tailTrace_2971436 : CollatzResearch.WordTrace tailWord_2971436 prefixEnd_2971436 339061089349631439263249 := by
  unfold tailWord_2971436
  simp only [CollatzResearch.WordTrace]
  refine ⟨54188587231501163855647081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72251449642001551807529441 54188587231501163855647081)
  ·
    refine ⟨40641440423625872891735311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54188587231501163855647081 40641440423625872891735311)
    ·
      refine ⟨60962160635438809337602967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40641440423625872891735311 60962160635438809337602967)
      ·
        refine ⟨91443240953158214006404451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60962160635438809337602967 91443240953158214006404451)
        ·
          refine ⟨137164861429737321009606677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91443240953158214006404451 137164861429737321009606677)
          ·
            refine ⟨6429602879518936922325313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 137164861429737321009606677 6429602879518936922325313)
            ·
              refine ⟨4822202159639202691743985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6429602879518936922325313 4822202159639202691743985)
              ·
                refine ⟨3616651619729402018807989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4822202159639202691743985 3616651619729402018807989)
                ·
                  refine ⟨339061089349631439263249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3616651619729402018807989 339061089349631439263249)
                  ·
                    rfl

theorem cell22_2971436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_2971436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971436 prefixEnd_2971436 := by exact prefixLift 2971436
  have htrace : WordTrace (prefixWord ++ tailWord_2971436) baseStart_2971436 baseEnd_2971436 := by
    simpa [prefixWord, tailWord_2971436, baseEnd_2971436] using wordTrace_append hprefix tailTrace_2971436
  have hstable : (prefixWord ++ tailWord_2971436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971436).length < 2 ^ (prefixWord ++ tailWord_2971436).sum := by decide
  have hdescent : baseEnd_2971436 < baseStart_2971436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971464 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 8]
def baseStart_2971464 : Nat := 118140960795 + 2971464 * 2 ^ 59
def prefixEnd_2971464 : Nat := 4983230072969 + 3 ^ 40 * 2971464 * 2
def baseEnd_2971464 : Nat := 339064284340370526029887

theorem tailTrace_2971464 : CollatzResearch.WordTrace tailWord_2971464 prefixEnd_2971464 339064284340370526029887 := by
  unfold tailWord_2971464
  simp only [CollatzResearch.WordTrace]
  refine ⟨54189097853450444246656723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72252130471267258995542297 54189097853450444246656723)
  ·
    refine ⟨81283646780175666369985085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54189097853450444246656723 81283646780175666369985085)
    ·
      refine ⟨30481367542565874888744407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81283646780175666369985085 30481367542565874888744407)
      ·
        refine ⟨45722051313848812333116611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30481367542565874888744407 45722051313848812333116611)
        ·
          refine ⟨68583076970773218499674917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45722051313848812333116611 68583076970773218499674917)
          ·
            refine ⟨12859326932019978468689047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68583076970773218499674917 12859326932019978468689047)
            ·
              refine ⟨19288990398029967703033571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12859326932019978468689047 19288990398029967703033571)
              ·
                refine ⟨28933485597044951554550357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19288990398029967703033571 28933485597044951554550357)
                ·
                  refine ⟨339064284340370526029887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28933485597044951554550357 339064284340370526029887)
                  ·
                    rfl

theorem cell22_2971464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 8].length) (baseStart_2971464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971464 prefixEnd_2971464 := by exact prefixLift 2971464
  have htrace : WordTrace (prefixWord ++ tailWord_2971464) baseStart_2971464 baseEnd_2971464 := by
    simpa [prefixWord, tailWord_2971464, baseEnd_2971464] using wordTrace_append hprefix tailTrace_2971464
  have hstable : (prefixWord ++ tailWord_2971464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971464).length < 2 ^ (prefixWord ++ tailWord_2971464).sum := by decide
  have hdescent : baseEnd_2971464 < baseStart_2971464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971466 : List Nat := [3, 1, 2, 1, 1, 1, 4, 4, 1, 4]
def baseStart_2971466 : Nat := 118140960795 + 2971466 * 2 ^ 59
def prefixEnd_2971466 : Nat := 4983230072969 + 3 ^ 40 * 2971466 * 2
def baseEnd_2971466 : Nat := 1017193537661984239539655

theorem tailTrace_2971466 : CollatzResearch.WordTrace tailWord_2971466 prefixEnd_2971466 1017193537661984239539655 := by
  unfold tailWord_2971466
  simp only [CollatzResearch.WordTrace]
  refine ⟨27094567163223410708721563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72252179101929095223257501 27094567163223410708721563)
  ·
    refine ⟨40641850744835116063082345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27094567163223410708721563 40641850744835116063082345)
    ·
      refine ⟨30481388058626337047311759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40641850744835116063082345 30481388058626337047311759)
      ·
        refine ⟨45722082087939505570967639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30481388058626337047311759 45722082087939505570967639)
        ·
          refine ⟨68583123131909258356451459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45722082087939505570967639 68583123131909258356451459)
          ·
            refine ⟨102874684697863887534677189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68583123131909258356451459 102874684697863887534677189)
            ·
              refine ⟨19289003380849478912751973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102874684697863887534677189 19289003380849478912751973)
              ·
                refine ⟨3616688133909277296140995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19289003380849478912751973 3616688133909277296140995)
                ·
                  refine ⟨5425032200863915944211493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3616688133909277296140995 5425032200863915944211493)
                  ·
                    refine ⟨1017193537661984239539655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5425032200863915944211493 1017193537661984239539655)
                    ·
                      rfl

theorem cell22_2971466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_2971466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971466 prefixEnd_2971466 := by exact prefixLift 2971466
  have htrace : WordTrace (prefixWord ++ tailWord_2971466) baseStart_2971466 baseEnd_2971466 := by
    simpa [prefixWord, tailWord_2971466, baseEnd_2971466] using wordTrace_append hprefix tailTrace_2971466
  have hstable : (prefixWord ++ tailWord_2971466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971466).length < 2 ^ (prefixWord ++ tailWord_2971466).sum := by decide
  have hdescent : baseEnd_2971466 < baseStart_2971466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971560 : List Nat := [2, 1, 6, 2, 1, 1, 2, 7]
def baseStart_2971560 : Nat := 118140960795 + 2971560 * 2 ^ 59
def prefixEnd_2971560 : Nat := 4983230072969 + 3 ^ 40 * 2971560 * 2
def baseEnd_2971560 : Nat := 113025079531444369743263

theorem tailTrace_2971560 : CollatzResearch.WordTrace tailWord_2971560 prefixEnd_2971560 113025079531444369743263 := by
  unfold tailWord_2971560
  simp only [CollatzResearch.WordTrace]
  refine ⟨54190848557276548444404067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72254464743035397925872089 54190848557276548444404067)
  ·
    refine ⟨81286272835914822666606101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54190848557276548444404067 81286272835914822666606101)
    ·
      refine ⟨3810294039183507312497161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81286272835914822666606101 3810294039183507312497161)
      ·
        refine ⟨2857720529387630484372871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3810294039183507312497161 2857720529387630484372871)
        ·
          refine ⟨4286580794081445726559307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2857720529387630484372871 4286580794081445726559307)
          ·
            refine ⟨6429871191122168589838961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4286580794081445726559307 6429871191122168589838961)
            ·
              refine ⟨4822403393341626442379221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6429871191122168589838961 4822403393341626442379221)
              ·
                refine ⟨113025079531444369743263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4822403393341626442379221 113025079531444369743263)
                ·
                  rfl

theorem cell22_2971560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 7].length) (baseStart_2971560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971560 prefixEnd_2971560 := by exact prefixLift 2971560
  have htrace : WordTrace (prefixWord ++ tailWord_2971560) baseStart_2971560 baseEnd_2971560 := by
    simpa [prefixWord, tailWord_2971560, baseEnd_2971560] using wordTrace_append hprefix tailTrace_2971560
  have hstable : (prefixWord ++ tailWord_2971560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971560).length < 2 ^ (prefixWord ++ tailWord_2971560).sum := by decide
  have hdescent : baseEnd_2971560 < baseStart_2971560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971571 : List Nat := [1, 1, 1, 2, 3, 1, 5, 3, 5]
def baseStart_2971571 : Nat := 118140960795 + 2971571 * 2 ^ 59
def prefixEnd_2971571 : Nat := 4983230072969 + 3 ^ 40 * 2971571 * 2
def baseEnd_2971571 : Nat := 339076493769266321888111

theorem tailTrace_2971571 : CollatzResearch.WordTrace tailWord_2971571 prefixEnd_2971571 339076493769266321888111 := by
  unfold tailWord_2971571
  simp only [CollatzResearch.WordTrace]
  refine ⟨108382098317513245767458567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72254732211675497178305711 108382098317513245767458567)
  ·
    refine ⟨162573147476269868651187851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108382098317513245767458567 162573147476269868651187851)
    ·
      refine ⟨243859721214404802976781777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162573147476269868651187851 243859721214404802976781777)
      ·
        refine ⟨182894790910803602232586333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243859721214404802976781777 182894790910803602232586333)
        ·
          refine ⟨68585546591551350837219875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182894790910803602232586333 68585546591551350837219875)
          ·
            refine ⟨102878319887327026255829813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68585546591551350837219875 102878319887327026255829813)
            ·
              refine ⟨9644842489436908711484045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102878319887327026255829813 9644842489436908711484045)
              ·
                refine ⟨3616815933538840766806517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9644842489436908711484045 3616815933538840766806517)
                ·
                  refine ⟨339076493769266321888111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3616815933538840766806517 339076493769266321888111)
                  ·
                    rfl

theorem cell22_2971571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 5].length) (baseStart_2971571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971571 prefixEnd_2971571 := by exact prefixLift 2971571
  have htrace : WordTrace (prefixWord ++ tailWord_2971571) baseStart_2971571 baseEnd_2971571 := by
    simpa [prefixWord, tailWord_2971571, baseEnd_2971571] using wordTrace_append hprefix tailTrace_2971571
  have hstable : (prefixWord ++ tailWord_2971571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971571).length < 2 ^ (prefixWord ++ tailWord_2971571).sum := by decide
  have hdescent : baseEnd_2971571 < baseStart_2971571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971609 : List Nat := [1, 2, 1, 2, 6, 2, 2, 2, 1, 3]
def baseStart_2971609 : Nat := 118140960795 + 2971609 * 2 ^ 59
def prefixEnd_2971609 : Nat := 4983230072969 + 3 ^ 40 * 2971609 * 2
def baseEnd_2971609 : Nat := 1017242489484379533214217

theorem tailTrace_2971609 : CollatzResearch.WordTrace tailWord_2971609 prefixEnd_2971609 1017242489484379533214217 := by
  unfold tailWord_2971609
  simp only [CollatzResearch.WordTrace]
  refine ⟨108383484291375578257341881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72255656194250385504894587 108383484291375578257341881)
  ·
    refine ⟨81287613218531683693006411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108383484291375578257341881 81287613218531683693006411)
    ·
      refine ⟨121931419827797525539509617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81287613218531683693006411 121931419827797525539509617)
      ·
        refine ⟨91448564870848144154632213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121931419827797525539509617 91448564870848144154632213)
        ·
          refine ⟨4286651478321006757248385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91448564870848144154632213 4286651478321006757248385)
          ·
            refine ⟨3214988608740755067936289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4286651478321006757248385 3214988608740755067936289)
            ·
              refine ⟨2411241456555566300952217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3214988608740755067936289 2411241456555566300952217)
              ·
                refine ⟨1808431092416674725714163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2411241456555566300952217 1808431092416674725714163)
                ·
                  refine ⟨2712646638625012088571245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1808431092416674725714163 2712646638625012088571245)
                  ·
                    refine ⟨1017242489484379533214217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2712646638625012088571245 1017242489484379533214217)
                    ·
                      rfl

theorem cell22_2971609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 1, 3].length) (baseStart_2971609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971609 prefixEnd_2971609 := by exact prefixLift 2971609
  have htrace : WordTrace (prefixWord ++ tailWord_2971609) baseStart_2971609 baseEnd_2971609 := by
    simpa [prefixWord, tailWord_2971609, baseEnd_2971609] using wordTrace_append hprefix tailTrace_2971609
  have hstable : (prefixWord ++ tailWord_2971609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971609).length < 2 ^ (prefixWord ++ tailWord_2971609).sum := by decide
  have hdescent : baseEnd_2971609 < baseStart_2971609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971633 : List Nat := [1, 2, 2, 2, 5, 1, 1, 2, 6]
def baseStart_2971633 : Nat := 118140960795 + 2971633 * 2 ^ 59
def prefixEnd_2971633 : Nat := 4983230072969 + 3 ^ 40 * 2971633 * 2
def baseEnd_2971633 : Nat := 339083568391617156871381

theorem tailTrace_2971633 : CollatzResearch.WordTrace tailWord_2971633 prefixEnd_2971633 339083568391617156871381 := by
  unfold tailWord_2971633
  simp only [CollatzResearch.WordTrace]
  refine ⟨108384359643288630356215553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72256239762192420237477035 108384359643288630356215553)
  ·
    refine ⟨81288269732466472767161665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108384359643288630356215553 81288269732466472767161665)
    ·
      refine ⟨60966202299349854575371249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81288269732466472767161665 60966202299349854575371249)
      ·
        refine ⟨45724651724512390931528437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60966202299349854575371249 45724651724512390931528437)
        ·
          refine ⟨4286686099173036649830791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45724651724512390931528437 4286686099173036649830791)
          ·
            refine ⟨6430029148759554974746187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4286686099173036649830791 6430029148759554974746187)
            ·
              refine ⟨9645043723139332462119281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6430029148759554974746187 9645043723139332462119281)
              ·
                refine ⟨7233782792354499346589461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9645043723139332462119281 7233782792354499346589461)
                ·
                  refine ⟨339083568391617156871381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7233782792354499346589461 339083568391617156871381)
                  ·
                    rfl

theorem cell22_2971633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 6].length) (baseStart_2971633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971633 prefixEnd_2971633 := by exact prefixLift 2971633
  have htrace : WordTrace (prefixWord ++ tailWord_2971633) baseStart_2971633 baseEnd_2971633 := by
    simpa [prefixWord, tailWord_2971633, baseEnd_2971633] using wordTrace_append hprefix tailTrace_2971633
  have hstable : (prefixWord ++ tailWord_2971633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971633).length < 2 ^ (prefixWord ++ tailWord_2971633).sum := by decide
  have hdescent : baseEnd_2971633 < baseStart_2971633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971652 : List Nat := [2, 3, 2, 4, 1, 1, 1, 3, 1, 4]
def baseStart_2971652 : Nat := 118140960795 + 2971652 * 2 ^ 59
def prefixEnd_2971652 : Nat := 4983230072969 + 3 ^ 40 * 2971652 * 2
def baseEnd_2971652 : Nat := 1017257209263141754389085

theorem tailTrace_2971652 : CollatzResearch.WordTrace tailWord_2971652 prefixEnd_2971652 1017257209263141754389085 := by
  unfold tailWord_2971652
  simp only [CollatzResearch.WordTrace]
  refine ⟨54192526315109898300578605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72256701753479864400771473 54192526315109898300578605)
  ·
    refine ⟨20322197368166211862716977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54192526315109898300578605 20322197368166211862716977)
    ·
      refine ⟨15241648026124658897037733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20322197368166211862716977 15241648026124658897037733)
      ·
        refine ⟨2857809004898373543194575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15241648026124658897037733 2857809004898373543194575)
        ·
          refine ⟨4286713507347560314791863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2857809004898373543194575 4286713507347560314791863)
          ·
            refine ⟨6430070261021340472187795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4286713507347560314791863 6430070261021340472187795)
            ·
              refine ⟨9645105391532010708281693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6430070261021340472187795 9645105391532010708281693)
              ·
                refine ⟨3616914521824504015605635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9645105391532010708281693 3616914521824504015605635)
                ·
                  refine ⟨5425371782736756023408453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3616914521824504015605635 5425371782736756023408453)
                  ·
                    refine ⟨1017257209263141754389085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5425371782736756023408453 1017257209263141754389085)
                    ·
                      rfl

theorem cell22_2971652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_2971652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971652 prefixEnd_2971652 := by exact prefixLift 2971652
  have htrace : WordTrace (prefixWord ++ tailWord_2971652) baseStart_2971652 baseEnd_2971652 := by
    simpa [prefixWord, tailWord_2971652, baseEnd_2971652] using wordTrace_append hprefix tailTrace_2971652
  have hstable : (prefixWord ++ tailWord_2971652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971652).length < 2 ^ (prefixWord ++ tailWord_2971652).sum := by decide
  have hdescent : baseEnd_2971652 < baseStart_2971652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971682 : List Nat := [3, 3, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_2971682 : Nat := 118140960795 + 2971682 * 2 ^ 59
def prefixEnd_2971682 : Nat := 4983230072969 + 3 ^ 40 * 2971682 * 2
def baseEnd_2971682 : Nat := 1017267478876231676138993

theorem tailTrace_2971682 : CollatzResearch.WordTrace tailWord_2971682 prefixEnd_2971682 1017267478876231676138993 := by
  unfold tailWord_2971682
  simp only [CollatzResearch.WordTrace]
  refine ⟨27096536705027777931187325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72257431213407407816499533 27096536705027777931187325)
  ·
    refine ⟨10161201264385416724195247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27096536705027777931187325 10161201264385416724195247)
    ·
      refine ⟨15241801896578125086292871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10161201264385416724195247 15241801896578125086292871)
      ·
        refine ⟨22862702844867187629439307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15241801896578125086292871 22862702844867187629439307)
        ·
          refine ⟨34294054267300781444158961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22862702844867187629439307 34294054267300781444158961)
          ·
            refine ⟨25720540700475586083119221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34294054267300781444158961 25720540700475586083119221)
            ·
              refine ⟨2411300690669586195292427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25720540700475586083119221 2411300690669586195292427)
              ·
                refine ⟨3616951036004379292938641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411300690669586195292427 3616951036004379292938641)
                ·
                  refine ⟨2712713277003284469703981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3616951036004379292938641 2712713277003284469703981)
                  ·
                    refine ⟨1017267478876231676138993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2712713277003284469703981 1017267478876231676138993)
                    ·
                      rfl

theorem cell22_2971682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_2971682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971682 prefixEnd_2971682 := by exact prefixLift 2971682
  have htrace : WordTrace (prefixWord ++ tailWord_2971682) baseStart_2971682 baseEnd_2971682 := by
    simpa [prefixWord, tailWord_2971682, baseEnd_2971682] using wordTrace_append hprefix tailTrace_2971682
  have hstable : (prefixWord ++ tailWord_2971682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971682).length < 2 ^ (prefixWord ++ tailWord_2971682).sum := by decide
  have hdescent : baseEnd_2971682 < baseStart_2971682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971740 : List Nat := [2, 2, 4, 1, 1, 3, 1, 3, 5]
def baseStart_2971740 : Nat := 118140960795 + 2971740 * 2 ^ 59
def prefixEnd_2971740 : Nat := 4983230072969 + 3 ^ 40 * 2971740 * 2
def baseEnd_2971740 : Nat := 339095777820512952729605

theorem tailTrace_2971740 : CollatzResearch.WordTrace tailWord_2971740 prefixEnd_2971740 339095777820512952729605 := by
  unfold tailWord_2971740
  simp only [CollatzResearch.WordTrace]
  refine ⟨54194131126950493815180337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72258841502600658420240449 54194131126950493815180337)
  ·
    refine ⟨40645598345212870361385253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54194131126950493815180337 40645598345212870361385253)
    ·
      refine ⟨7621049689727413192759735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40645598345212870361385253 7621049689727413192759735)
      ·
        refine ⟨11431574534591119789139603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7621049689727413192759735 11431574534591119789139603)
        ·
          refine ⟨17147361801886679683709405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11431574534591119789139603 17147361801886679683709405)
          ·
            refine ⟨6430260675707504881391027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17147361801886679683709405 6430260675707504881391027)
            ·
              refine ⟨9645391013561257322086541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6430260675707504881391027 9645391013561257322086541)
              ·
                refine ⟨3617021630085471495782453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9645391013561257322086541 3617021630085471495782453)
                ·
                  refine ⟨339095777820512952729605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3617021630085471495782453 339095777820512952729605)
                  ·
                    rfl

theorem cell22_2971740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_2971740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971740 prefixEnd_2971740 := by exact prefixLift 2971740
  have htrace : WordTrace (prefixWord ++ tailWord_2971740) baseStart_2971740 baseEnd_2971740 := by
    simpa [prefixWord, tailWord_2971740, baseEnd_2971740] using wordTrace_append hprefix tailTrace_2971740
  have hstable : (prefixWord ++ tailWord_2971740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971740).length < 2 ^ (prefixWord ++ tailWord_2971740).sum := by decide
  have hdescent : baseEnd_2971740 < baseStart_2971740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971753 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 3, 4]
def baseStart_2971753 : Nat := 118140960795 + 2971753 * 2 ^ 59
def prefixEnd_2971753 : Nat := 4983230072969 + 3 ^ 40 * 2971753 * 2
def baseEnd_2971753 : Nat := 1017291783627211157613775

theorem tailTrace_2971753 : CollatzResearch.WordTrace tailWord_2971753 prefixEnd_2971753 1017291783627211157613775 := by
  unfold tailWord_2971753
  simp only [CollatzResearch.WordTrace]
  refine ⟨108388736402853890850583913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72259157601902593900389275 108388736402853890850583913)
  ·
    refine ⟨81291552302140418137937935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108388736402853890850583913 81291552302140418137937935)
    ·
      refine ⟨121937328453210627206906903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81291552302140418137937935 121937328453210627206906903)
      ·
        refine ⟨182905992679815940810360355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121937328453210627206906903 182905992679815940810360355)
        ·
          refine ⟨274358989019723911215540533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182905992679815940810360355 274358989019723911215540533)
          ·
            refine ⟨25721155220599116676456925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 274358989019723911215540533 25721155220599116676456925)
            ·
              refine ⟨9645433207724668753671347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25721155220599116676456925 9645433207724668753671347)
              ·
                refine ⟨14468149811587003130507021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9645433207724668753671347 14468149811587003130507021)
                ·
                  refine ⟨5425556179345126173940133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14468149811587003130507021 5425556179345126173940133)
                  ·
                    refine ⟨1017291783627211157613775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5425556179345126173940133 1017291783627211157613775)
                    ·
                      rfl

theorem cell22_2971753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_2971753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971753 prefixEnd_2971753 := by exact prefixLift 2971753
  have htrace : WordTrace (prefixWord ++ tailWord_2971753) baseStart_2971753 baseEnd_2971753 := by
    simpa [prefixWord, tailWord_2971753, baseEnd_2971753] using wordTrace_append hprefix tailTrace_2971753
  have hstable : (prefixWord ++ tailWord_2971753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971753).length < 2 ^ (prefixWord ++ tailWord_2971753).sum := by decide
  have hdescent : baseEnd_2971753 < baseStart_2971753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971785 : List Nat := [1, 2, 1, 1, 4, 2, 3, 4, 4]
def baseStart_2971785 : Nat := 118140960795 + 2971785 * 2 ^ 59
def prefixEnd_2971785 : Nat := 4983230072969 + 3 ^ 40 * 2971785 * 2
def baseEnd_2971785 : Nat := 339100912627057913604559

theorem tailTrace_2971785 : CollatzResearch.WordTrace tailWord_2971785 prefixEnd_2971785 339100912627057913604559 := by
  unfold tailWord_2971785
  simp only [CollatzResearch.WordTrace]
  refine ⟨108389903538737960315748809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72259935692491973543832539 108389903538737960315748809)
  ·
    refine ⟨81292427654053470236811607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108389903538737960315748809 81292427654053470236811607)
    ·
      refine ⟨121938641481080205355217411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81292427654053470236811607 121938641481080205355217411)
      ·
        refine ⟨182907962221620308032826117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121938641481080205355217411 182907962221620308032826117)
        ·
          refine ⟨34295242916553807756154897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182907962221620308032826117 34295242916553807756154897)
          ·
            refine ⟨25721432187415355817116173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34295242916553807756154897 25721432187415355817116173)
            ·
              refine ⟨9645537070280758431418565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25721432187415355817116173 9645537070280758431418565)
              ·
                refine ⟨1808538200677642205890981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9645537070280758431418565 1808538200677642205890981)
                ·
                  refine ⟨339100912627057913604559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1808538200677642205890981 339100912627057913604559)
                  ·
                    rfl

theorem cell22_2971785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 4].length) (baseStart_2971785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971785 prefixEnd_2971785 := by exact prefixLift 2971785
  have htrace : WordTrace (prefixWord ++ tailWord_2971785) baseStart_2971785 baseEnd_2971785 := by
    simpa [prefixWord, tailWord_2971785, baseEnd_2971785] using wordTrace_append hprefix tailTrace_2971785
  have hstable : (prefixWord ++ tailWord_2971785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971785).length < 2 ^ (prefixWord ++ tailWord_2971785).sum := by decide
  have hdescent : baseEnd_2971785 < baseStart_2971785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971845 : List Nat := [1, 3, 1, 1, 1, 1, 5, 3, 3, 3]
def baseStart_2971845 : Nat := 118140960795 + 2971845 * 2 ^ 59
def prefixEnd_2971845 : Nat := 4983230072969 + 3 ^ 40 * 2971845 * 2
def baseEnd_2971845 : Nat := 1017323277107353584313493

theorem tailTrace_2971845 : CollatzResearch.WordTrace tailWord_2971845 prefixEnd_2971845 1017323277107353584313493 := by
  unfold tailWord_2971845
  simp only [CollatzResearch.WordTrace]
  refine ⟨108392091918520590562932989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72261394612347060375288659 108392091918520590562932989)
  ·
    refine ⟨40647034469445221461099871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108392091918520590562932989 40647034469445221461099871)
    ·
      refine ⟨60970551704167832191649807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40647034469445221461099871 60970551704167832191649807)
      ·
        refine ⟨91455827556251748287474711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60970551704167832191649807 91455827556251748287474711)
        ·
          refine ⟨137183741334377622431212067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91455827556251748287474711 137183741334377622431212067)
          ·
            refine ⟨205775612001566433646818101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137183741334377622431212067 205775612001566433646818101)
            ·
              refine ⟨19291463625146853154389197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 205775612001566433646818101 19291463625146853154389197)
              ·
                refine ⟨7234298859430069932895949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19291463625146853154389197 7234298859430069932895949)
                ·
                  refine ⟨2712862072286276224835981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7234298859430069932895949 2712862072286276224835981)
                  ·
                    refine ⟨1017323277107353584313493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2712862072286276224835981 1017323277107353584313493)
                    ·
                      rfl

theorem cell22_2971845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_2971845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971845 prefixEnd_2971845 := by exact prefixLift 2971845
  have htrace : WordTrace (prefixWord ++ tailWord_2971845) baseStart_2971845 baseEnd_2971845 := by
    simpa [prefixWord, tailWord_2971845, baseEnd_2971845] using wordTrace_append hprefix tailTrace_2971845
  have hstable : (prefixWord ++ tailWord_2971845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971845).length < 2 ^ (prefixWord ++ tailWord_2971845).sum := by decide
  have hdescent : baseEnd_2971845 < baseStart_2971845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971905 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 3, 4]
def baseStart_2971905 : Nat := 118140960795 + 2971905 * 2 ^ 59
def prefixEnd_2971905 : Nat := 4983230072969 + 3 ^ 40 * 2971905 * 2
def baseEnd_2971905 : Nat := 1017343816333533427813309

theorem tailTrace_2971905 : CollatzResearch.WordTrace tailWord_2971905 prefixEnd_2971905 1017343816333533427813309 := by
  unfold tailWord_2971905
  simp only [CollatzResearch.WordTrace]
  refine ⟨108394280298303220810117169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72262853532202147206744779 108394280298303220810117169)
  ·
    refine ⟨81295710223727415607587877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108394280298303220810117169 81295710223727415607587877)
    ·
      refine ⟨15242945666948890426422727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81295710223727415607587877 15242945666948890426422727)
      ·
        refine ⟨22864418500423335639634091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15242945666948890426422727 22864418500423335639634091)
        ·
          refine ⟨34296627750635003459451137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22864418500423335639634091 34296627750635003459451137)
          ·
            refine ⟨25722470812976252594588353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34296627750635003459451137 25722470812976252594588353)
            ·
              refine ⟨19291853109732189445941265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25722470812976252594588353 19291853109732189445941265)
              ·
                refine ⟨14468889832299142084455949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19291853109732189445941265 14468889832299142084455949)
                ·
                  refine ⟨5425833687112178281670981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14468889832299142084455949 5425833687112178281670981)
                  ·
                    refine ⟨1017343816333533427813309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5425833687112178281670981 1017343816333533427813309)
                    ·
                      rfl

theorem cell22_2971905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_2971905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971905 prefixEnd_2971905 := by exact prefixLift 2971905
  have htrace : WordTrace (prefixWord ++ tailWord_2971905) baseStart_2971905 baseEnd_2971905 := by
    simpa [prefixWord, tailWord_2971905, baseEnd_2971905] using wordTrace_append hprefix tailTrace_2971905
  have hstable : (prefixWord ++ tailWord_2971905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971905).length < 2 ^ (prefixWord ++ tailWord_2971905).sum := by decide
  have hdescent : baseEnd_2971905 < baseStart_2971905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971935 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 3, 5]
def baseStart_2971935 : Nat := 118140960795 + 2971935 * 2 ^ 59
def prefixEnd_2971935 : Nat := 4983230072969 + 3 ^ 40 * 2971935 * 2
def baseEnd_2971935 : Nat := 1017354085946623349563217

theorem tailTrace_2971935 : CollatzResearch.WordTrace tailWord_2971935 prefixEnd_2971935 1017354085946623349563217 := by
  unfold tailWord_2971935
  simp only [CollatzResearch.WordTrace]
  refine ⟨108395374488194535933709259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72263582992129690622472839 108395374488194535933709259)
  ·
    refine ⟨162593061732291803900563889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108395374488194535933709259 162593061732291803900563889)
    ·
      refine ⟨121944796299218852925422917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162593061732291803900563889 121944796299218852925422917)
      ·
        refine ⟨22864649306103534923516797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121944796299218852925422917 22864649306103534923516797)
        ·
          refine ⟨8574243489788825596318799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22864649306103534923516797 8574243489788825596318799)
          ·
            refine ⟨12861365234683238394478199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8574243489788825596318799 12861365234683238394478199)
            ·
              refine ⟨19292047852024857591717299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12861365234683238394478199 19292047852024857591717299)
              ·
                refine ⟨28938071778037286387575949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19292047852024857591717299 28938071778037286387575949)
                ·
                  refine ⟨10851776916763982395340981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28938071778037286387575949 10851776916763982395340981)
                  ·
                    refine ⟨1017354085946623349563217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10851776916763982395340981 1017354085946623349563217)
                    ·
                      rfl

theorem cell22_2971935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_2971935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971935 prefixEnd_2971935 := by exact prefixLift 2971935
  have htrace : WordTrace (prefixWord ++ tailWord_2971935) baseStart_2971935 baseEnd_2971935 := by
    simpa [prefixWord, tailWord_2971935, baseEnd_2971935] using wordTrace_append hprefix tailTrace_2971935
  have hstable : (prefixWord ++ tailWord_2971935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971935).length < 2 ^ (prefixWord ++ tailWord_2971935).sum := by decide
  have hdescent : baseEnd_2971935 < baseStart_2971935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971954 : List Nat := [3, 2, 1, 1, 5, 1, 1, 4, 4]
def baseStart_2971954 : Nat := 118140960795 + 2971954 * 2 ^ 59
def prefixEnd_2971954 : Nat := 4983230072969 + 3 ^ 40 * 2971954 * 2
def baseEnd_2971954 : Nat := 339120196678304544446053

theorem tailTrace_2971954 : CollatzResearch.WordTrace tailWord_2971954 prefixEnd_2971954 339120196678304544446053 := by
  unfold tailWord_2971954
  simp only [CollatzResearch.WordTrace]
  refine ⟨27099016868781425544662729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72264044983417134785767277 27099016868781425544662729)
  ·
    refine ⟨20324262651586069158497047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27099016868781425544662729 20324262651586069158497047)
    ·
      refine ⟨30486393977379103737745571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20324262651586069158497047 30486393977379103737745571)
      ·
        refine ⟨45729590966068655606618357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30486393977379103737745571 45729590966068655606618357)
        ·
          refine ⟨4287149153068936463120471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45729590966068655606618357 4287149153068936463120471)
          ·
            refine ⟨6430723729603404694680707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4287149153068936463120471 6430723729603404694680707)
            ·
              refine ⟨9646085594405107042021061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6430723729603404694680707 9646085594405107042021061)
              ·
                refine ⟨1808641048950957570378949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9646085594405107042021061 1808641048950957570378949)
                ·
                  refine ⟨339120196678304544446053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1808641048950957570378949 339120196678304544446053)
                  ·
                    rfl

theorem cell22_2971954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_2971954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971954 prefixEnd_2971954 := by exact prefixLift 2971954
  have htrace : WordTrace (prefixWord ++ tailWord_2971954) baseStart_2971954 baseEnd_2971954 := by
    simpa [prefixWord, tailWord_2971954, baseEnd_2971954] using wordTrace_append hprefix tailTrace_2971954
  have hstable : (prefixWord ++ tailWord_2971954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971954).length < 2 ^ (prefixWord ++ tailWord_2971954).sum := by decide
  have hdescent : baseEnd_2971954 < baseStart_2971954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971969 : List Nat := [1, 2, 5, 2, 2, 1, 2, 1, 1, 5]
def baseStart_2971969 : Nat := 118140960795 + 2971969 * 2 ^ 59
def prefixEnd_2971969 : Nat := 4983230072969 + 3 ^ 40 * 2971969 * 2
def baseEnd_2971969 : Nat := 1017365724841458594213113

theorem tailTrace_2971969 : CollatzResearch.WordTrace tailWord_2971969 prefixEnd_2971969 1017365724841458594213113 := by
  unfold tailWord_2971969
  simp only [CollatzResearch.WordTrace]
  refine ⟨108396614570071359740446961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72264409713380906493631307 108396614570071359740446961)
  ·
    refine ⟨81297460927553519805335221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108396614570071359740446961 81297460927553519805335221)
    ·
      refine ⟨7621636961958142481750177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81297460927553519805335221 7621636961958142481750177)
      ·
        refine ⟨5716227721468606861312633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7621636961958142481750177 5716227721468606861312633)
        ·
          refine ⟨4287170791101455145984475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5716227721468606861312633 4287170791101455145984475)
          ·
            refine ⟨6430756186652182718976713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4287170791101455145984475 6430756186652182718976713)
            ·
              refine ⟨4823067139989137039232535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6430756186652182718976713 4823067139989137039232535)
              ·
                refine ⟨7234600709983705558848803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4823067139989137039232535 7234600709983705558848803)
                ·
                  refine ⟨10851901064975558338273205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7234600709983705558848803 10851901064975558338273205)
                  ·
                    refine ⟨1017365724841458594213113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10851901064975558338273205 1017365724841458594213113)
                    ·
                      rfl

theorem cell22_2971969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_2971969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971969 prefixEnd_2971969 := by exact prefixLift 2971969
  have htrace : WordTrace (prefixWord ++ tailWord_2971969) baseStart_2971969 baseEnd_2971969 := by
    simpa [prefixWord, tailWord_2971969, baseEnd_2971969] using wordTrace_append hprefix tailTrace_2971969
  have hstable : (prefixWord ++ tailWord_2971969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971969).length < 2 ^ (prefixWord ++ tailWord_2971969).sum := by decide
  have hdescent : baseEnd_2971969 < baseStart_2971969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972055 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 8]
def baseStart_2972055 : Nat := 118140960795 + 2972055 * 2 ^ 59
def prefixEnd_2972055 : Nat := 4983230072969 + 3 ^ 40 * 2972055 * 2
def baseEnd_2972055 : Nat := 339131721466327678854283

theorem tailTrace_2972055 : CollatzResearch.WordTrace tailWord_2972055 prefixEnd_2972055 339131721466327678854283 := by
  unfold tailWord_2972055
  simp only [CollatzResearch.WordTrace]
  refine ⟨108399751247759796428077619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72266500831839864285385079 108399751247759796428077619)
  ·
    refine ⟨162599626871639694642116429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108399751247759796428077619 162599626871639694642116429)
    ·
      refine ⟨60974860076864885490793661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162599626871639694642116429 60974860076864885490793661)
      ·
        refine ⟨22865572528824332059047623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60974860076864885490793661 22865572528824332059047623)
        ·
          refine ⟨34298358793236498088571435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22865572528824332059047623 34298358793236498088571435)
          ·
            refine ⟨51447538189854747132857153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34298358793236498088571435 51447538189854747132857153)
            ·
              refine ⟨38585653642391060349642865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51447538189854747132857153 38585653642391060349642865)
              ·
                refine ⟨28939240231793295262232149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38585653642391060349642865 28939240231793295262232149)
                ·
                  refine ⟨339131721466327678854283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28939240231793295262232149 339131721466327678854283)
                  ·
                    rfl

theorem cell22_2972055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 8].length) (baseStart_2972055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972055 prefixEnd_2972055 := by exact prefixLift 2972055
  have htrace : WordTrace (prefixWord ++ tailWord_2972055) baseStart_2972055 baseEnd_2972055 := by
    simpa [prefixWord, tailWord_2972055, baseEnd_2972055] using wordTrace_append hprefix tailTrace_2972055
  have hstable : (prefixWord ++ tailWord_2972055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972055).length < 2 ^ (prefixWord ++ tailWord_2972055).sum := by decide
  have hdescent : baseEnd_2972055 < baseStart_2972055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972057 : List Nat := [1, 2, 1, 2, 1, 4, 1, 5, 1, 4]
def baseStart_2972057 : Nat := 118140960795 + 2972057 * 2 ^ 59
def prefixEnd_2972057 : Nat := 4983230072969 + 3 ^ 40 * 2972057 * 2
def baseEnd_2972057 : Nat := 1017395849039855698012843

theorem tailTrace_2972057 : CollatzResearch.WordTrace tailWord_2972057 prefixEnd_2972057 1017395849039855698012843 := by
  unfold tailWord_2972057
  simp only [CollatzResearch.WordTrace]
  refine ⟨108399824193752550769650425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72266549462501700513100283 108399824193752550769650425)
  ·
    refine ⟨81299868145314413077237819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108399824193752550769650425 81299868145314413077237819)
    ·
      refine ⟨121949802217971619615856729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81299868145314413077237819 121949802217971619615856729)
      ·
        refine ⟨91462351663478714711892547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121949802217971619615856729 91462351663478714711892547)
        ·
          refine ⟨137193527495218072067838821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91462351663478714711892547 137193527495218072067838821)
          ·
            refine ⟨25723786405353388512719779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137193527495218072067838821 25723786405353388512719779)
            ·
              refine ⟨38585679608030082769079669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25723786405353388512719779 38585679608030082769079669)
              ·
                refine ⟨3617407463252820259601219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38585679608030082769079669 3617407463252820259601219)
                ·
                  refine ⟨5426111194879230389401829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3617407463252820259601219 5426111194879230389401829)
                  ·
                    refine ⟨1017395849039855698012843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5426111194879230389401829 1017395849039855698012843)
                    ·
                      rfl

theorem cell22_2972057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 4].length) (baseStart_2972057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972057 prefixEnd_2972057 := by exact prefixLift 2972057
  have htrace : WordTrace (prefixWord ++ tailWord_2972057) baseStart_2972057 baseEnd_2972057 := by
    simpa [prefixWord, tailWord_2972057, baseEnd_2972057] using wordTrace_append hprefix tailTrace_2972057
  have hstable : (prefixWord ++ tailWord_2972057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972057).length < 2 ^ (prefixWord ++ tailWord_2972057).sum := by decide
  have hdescent : baseEnd_2972057 < baseStart_2972057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972065 : List Nat := [1, 2, 3, 5, 1, 1, 3, 2, 1, 3]
def baseStart_2972065 : Nat := 118140960795 + 2972065 * 2 ^ 59
def prefixEnd_2972065 : Nat := 4983230072969 + 3 ^ 40 * 2972065 * 2
def baseEnd_2972065 : Nat := 1017398587603346343812819

theorem tailTrace_2972065 : CollatzResearch.WordTrace tailWord_2972065 prefixEnd_2972065 1017398587603346343812819 := by
  unfold tailWord_2972065
  simp only [CollatzResearch.WordTrace]
  refine ⟨108400115977723568135941649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72266743985149045423961099 108400115977723568135941649)
  ·
    refine ⟨81300086983292676101956237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108400115977723568135941649 81300086983292676101956237)
    ·
      refine ⟨30487532618734753538233589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81300086983292676101956237 30487532618734753538233589)
      ·
        refine ⟨2858206183006383144209399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30487532618734753538233589 2858206183006383144209399)
        ·
          refine ⟨4287309274509574716314099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2858206183006383144209399 4287309274509574716314099)
          ·
            refine ⟨6430963911764362074471149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4287309274509574716314099 6430963911764362074471149)
            ·
              refine ⟨2411611466911635777926681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6430963911764362074471149 2411611466911635777926681)
              ·
                refine ⟨1808708600183726833445011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2411611466911635777926681 1808708600183726833445011)
                ·
                  refine ⟨2713062900275590250167517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1808708600183726833445011 2713062900275590250167517)
                  ·
                    refine ⟨1017398587603346343812819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2713062900275590250167517 1017398587603346343812819)
                    ·
                      rfl

theorem cell22_2972065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_2972065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972065 prefixEnd_2972065 := by exact prefixLift 2972065
  have htrace : WordTrace (prefixWord ++ tailWord_2972065) baseStart_2972065 baseEnd_2972065 := by
    simpa [prefixWord, tailWord_2972065, baseEnd_2972065] using wordTrace_append hprefix tailTrace_2972065
  have hstable : (prefixWord ++ tailWord_2972065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972065).length < 2 ^ (prefixWord ++ tailWord_2972065).sum := by decide
  have hdescent : baseEnd_2972065 < baseStart_2972065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972115 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 6, 7]
def baseStart_2972115 : Nat := 118140960795 + 2972115 * 2 ^ 59
def prefixEnd_2972115 : Nat := 4983230072969 + 3 ^ 40 * 2972115 * 2
def baseEnd_2972115 : Nat := 1017415703625162880062665

theorem tailTrace_2972115 : CollatzResearch.WordTrace tailWord_2972115 prefixEnd_2972115 1017415703625162880062665 := by
  unfold tailWord_2972115
  simp only [CollatzResearch.WordTrace]
  refine ⟨108401939627542426675261799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72267959751694951116841199 108401939627542426675261799)
  ·
    refine ⟨162602909441313640012892699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108401939627542426675261799 162602909441313640012892699)
    ·
      refine ⟨243904364161970460019339049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162602909441313640012892699 243904364161970460019339049)
      ·
        refine ⟨182928273121477845014504287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243904364161970460019339049 182928273121477845014504287)
        ·
          refine ⟨274392409682216767521756431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182928273121477845014504287 274392409682216767521756431)
          ·
            refine ⟨411588614523325151282634647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274392409682216767521756431 411588614523325151282634647)
            ·
              refine ⟨617382921784987726923951971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411588614523325151282634647 617382921784987726923951971)
              ·
                refine ⟨926074382677481590385927957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 617382921784987726923951971 926074382677481590385927957)
                ·
                  refine ⟨43409736688006949549340373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 926074382677481590385927957 43409736688006949549340373)
                  ·
                    refine ⟨1017415703625162880062665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43409736688006949549340373 1017415703625162880062665)
                    ·
                      rfl

theorem cell22_2972115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 7].length) (baseStart_2972115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972115 prefixEnd_2972115 := by exact prefixLift 2972115
  have htrace : WordTrace (prefixWord ++ tailWord_2972115) baseStart_2972115 baseEnd_2972115 := by
    simpa [prefixWord, tailWord_2972115, baseEnd_2972115] using wordTrace_append hprefix tailTrace_2972115
  have hstable : (prefixWord ++ tailWord_2972115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972115).length < 2 ^ (prefixWord ++ tailWord_2972115).sum := by decide
  have hdescent : baseEnd_2972115 < baseStart_2972115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972183 : List Nat := [1, 1, 3, 6, 1, 1, 2, 1, 3, 3]
def baseStart_2972183 : Nat := 118140960795 + 2972183 * 2 ^ 59
def prefixEnd_2972183 : Nat := 4983230072969 + 3 ^ 40 * 2972183 * 2
def baseEnd_2972183 : Nat := 1017438981414833369362457

theorem tailTrace_2972183 : CollatzResearch.WordTrace tailWord_2972183 prefixEnd_2972183 1017438981414833369362457 := by
  unfold tailWord_2972183
  simp only [CollatzResearch.WordTrace]
  refine ⟨108404419791296074288737203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72269613194197382859158135 108404419791296074288737203)
  ·
    refine ⟨162606629686944111433105805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108404419791296074288737203 162606629686944111433105805)
    ·
      refine ⟨60977486132604041787414677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162606629686944111433105805 60977486132604041787414677)
      ·
        refine ⟨2858319662465814458785063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60977486132604041787414677 2858319662465814458785063)
        ·
          refine ⟨4287479493698721688177595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2858319662465814458785063 4287479493698721688177595)
          ·
            refine ⟨6431219240548082532266393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4287479493698721688177595 6431219240548082532266393)
            ·
              refine ⟨4823414430411061899199795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6431219240548082532266393 4823414430411061899199795)
              ·
                refine ⟨7235121645616592848799693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4823414430411061899199795 7235121645616592848799693)
                ·
                  refine ⟨2713170617106222318299885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7235121645616592848799693 2713170617106222318299885)
                  ·
                    refine ⟨1017438981414833369362457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2713170617106222318299885 1017438981414833369362457)
                    ·
                      rfl

theorem cell22_2972183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_2972183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972183 prefixEnd_2972183 := by exact prefixLift 2972183
  have htrace : WordTrace (prefixWord ++ tailWord_2972183) baseStart_2972183 baseEnd_2972183 := by
    simpa [prefixWord, tailWord_2972183, baseEnd_2972183] using wordTrace_append hprefix tailTrace_2972183
  have hstable : (prefixWord ++ tailWord_2972183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972183).length < 2 ^ (prefixWord ++ tailWord_2972183).sum := by decide
  have hdescent : baseEnd_2972183 < baseStart_2972183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972209 : List Nat := [1, 2, 2, 3, 1, 1, 3, 4, 1, 4]
def baseStart_2972209 : Nat := 118140960795 + 2972209 * 2 ^ 59
def prefixEnd_2972209 : Nat := 4983230072969 + 3 ^ 40 * 2972209 * 2
def baseEnd_2972209 : Nat := 1017447881746177968212377

theorem tailTrace_2972209 : CollatzResearch.WordTrace tailWord_2972209 prefixEnd_2972209 1017447881746177968212377 := by
  unfold tailWord_2972209
  simp only [CollatzResearch.WordTrace]
  refine ⟨108405368089201880729183681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72270245392801253819455787 108405368089201880729183681)
  ·
    refine ⟨81304026066901410546887761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108405368089201880729183681 81304026066901410546887761)
    ·
      refine ⟨60978019550176057910165821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81304026066901410546887761 60978019550176057910165821)
      ·
        refine ⟨22866757331316021716312183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60978019550176057910165821 22866757331316021716312183)
        ·
          refine ⟨34300135996974032574468275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22866757331316021716312183 34300135996974032574468275)
          ·
            refine ⟨51450203995461048861702413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34300135996974032574468275 51450203995461048861702413)
            ·
              refine ⟨19293826498297893323138405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51450203995461048861702413 19293826498297893323138405)
              ·
                refine ⟨3617592468430854998088451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19293826498297893323138405 3617592468430854998088451)
                ·
                  refine ⟨5426388702646282497132677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3617592468430854998088451 5426388702646282497132677)
                  ·
                    refine ⟨1017447881746177968212377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5426388702646282497132677 1017447881746177968212377)
                    ·
                      rfl

theorem cell22_2972209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_2972209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972209 prefixEnd_2972209 := by exact prefixLift 2972209
  have htrace : WordTrace (prefixWord ++ tailWord_2972209) baseStart_2972209 baseEnd_2972209 := by
    simpa [prefixWord, tailWord_2972209, baseEnd_2972209] using wordTrace_append hprefix tailTrace_2972209
  have hstable : (prefixWord ++ tailWord_2972209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972209).length < 2 ^ (prefixWord ++ tailWord_2972209).sum := by decide
  have hdescent : baseEnd_2972209 < baseStart_2972209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972239 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 4, 3]
def baseStart_2972239 : Nat := 118140960795 + 2972239 * 2 ^ 59
def prefixEnd_2972239 : Nat := 4983230072969 + 3 ^ 40 * 2972239 * 2
def baseEnd_2972239 : Nat := 1017458151359267889962285

theorem tailTrace_2972239 : CollatzResearch.WordTrace tailWord_2972239 prefixEnd_2972239 1017458151359267889962285 := by
  unfold tailWord_2972239
  simp only [CollatzResearch.WordTrace]
  refine ⟨108406462279093195852775771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72270974852728797235183847 108406462279093195852775771)
  ·
    refine ⟨162609693418639793779163657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108406462279093195852775771 162609693418639793779163657)
    ·
      refine ⟨121957270063979845334372743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162609693418639793779163657 121957270063979845334372743)
      ·
        refine ⟨182935905095969768001559115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121957270063979845334372743 182935905095969768001559115)
        ·
          refine ⟨274403857643954652002338673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182935905095969768001559115 274403857643954652002338673)
          ·
            refine ⟨205802893232965989001754005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274403857643954652002338673 205802893232965989001754005)
            ·
              refine ⟨9647010620295280734457219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 205802893232965989001754005 9647010620295280734457219)
              ·
                refine ⟨14470515930442921101685829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9647010620295280734457219 14470515930442921101685829)
                ·
                  refine ⟨2713221736958047706566093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14470515930442921101685829 2713221736958047706566093)
                  ·
                    refine ⟨1017458151359267889962285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2713221736958047706566093 1017458151359267889962285)
                    ·
                      rfl

theorem cell22_2972239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 3].length) (baseStart_2972239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972239 prefixEnd_2972239 := by exact prefixLift 2972239
  have htrace : WordTrace (prefixWord ++ tailWord_2972239) baseStart_2972239 baseEnd_2972239 := by
    simpa [prefixWord, tailWord_2972239, baseEnd_2972239] using wordTrace_append hprefix tailTrace_2972239
  have hstable : (prefixWord ++ tailWord_2972239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972239).length < 2 ^ (prefixWord ++ tailWord_2972239).sum := by decide
  have hdescent : baseEnd_2972239 < baseStart_2972239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972269 : List Nat := [1, 5, 1, 1, 3, 1, 2, 8]
def baseStart_2972269 : Nat := 118140960795 + 2972269 * 2 ^ 59
def prefixEnd_2972269 : Nat := 4983230072969 + 3 ^ 40 * 2972269 * 2
def baseEnd_2972269 : Nat := 113052046774706423523577

theorem tailTrace_2972269 : CollatzResearch.WordTrace tailWord_2972269 prefixEnd_2972269 113052046774706423523577 := by
  unfold tailWord_2972269
  simp only [CollatzResearch.WordTrace]
  refine ⟨108407556468984510976367861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72271704312656340650911907 108407556468984510976367861)
  ·
    refine ⟨10163208418967297904034487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108407556468984510976367861 10163208418967297904034487)
    ·
      refine ⟨15244812628450946856051731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10163208418967297904034487 15244812628450946856051731)
      ·
        refine ⟨22867218942676420284077597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15244812628450946856051731 22867218942676420284077597)
        ·
          refine ⟨8575207103503657606529099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22867218942676420284077597 8575207103503657606529099)
          ·
            refine ⟨12862810655255486409793649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8575207103503657606529099 12862810655255486409793649)
            ·
              refine ⟨9647107991441614807345237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12862810655255486409793649 9647107991441614807345237)
              ·
                refine ⟨113052046774706423523577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9647107991441614807345237 113052046774706423523577)
                ·
                  rfl

theorem cell22_2972269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 8].length) (baseStart_2972269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972269 prefixEnd_2972269 := by exact prefixLift 2972269
  have htrace : WordTrace (prefixWord ++ tailWord_2972269) baseStart_2972269 baseEnd_2972269 := by
    simpa [prefixWord, tailWord_2972269, baseEnd_2972269] using wordTrace_append hprefix tailTrace_2972269
  have hstable : (prefixWord ++ tailWord_2972269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972269).length < 2 ^ (prefixWord ++ tailWord_2972269).sum := by decide
  have hdescent : baseEnd_2972269 < baseStart_2972269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972318 : List Nat := [4, 3, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_2972318 : Nat := 118140960795 + 2972318 * 2 ^ 59
def prefixEnd_2972318 : Nat := 4983230072969 + 3 ^ 40 * 2972318 * 2
def baseEnd_2972318 : Nat := 1017485194673738017237043

theorem tailTrace_2972318 : CollatzResearch.WordTrace tailWord_2972318 prefixEnd_2972318 1017485194673738017237043 := by
  unfold tailWord_2972318
  simp only [CollatzResearch.WordTrace]
  refine ⟨13551167955725874043112701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72272895763871328229934405 13551167955725874043112701)
  ·
    refine ⟨5081687983397202766167263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13551167955725874043112701 5081687983397202766167263)
    ·
      refine ⟨7622531975095804149250895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5081687983397202766167263 7622531975095804149250895)
      ·
        refine ⟨11433797962643706223876343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7622531975095804149250895 11433797962643706223876343)
        ·
          refine ⟨17150696943965559335814515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11433797962643706223876343 17150696943965559335814515)
          ·
            refine ⟨25726045415948339003721773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17150696943965559335814515 25726045415948339003721773)
            ·
              refine ⟨9647267030980627126395665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25726045415948339003721773 9647267030980627126395665)
              ·
                refine ⟨7235450273235470344796749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9647267030980627126395665 7235450273235470344796749)
                ·
                  refine ⟨2713293852463301379298781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7235450273235470344796749 2713293852463301379298781)
                  ·
                    refine ⟨1017485194673738017237043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2713293852463301379298781 1017485194673738017237043)
                    ·
                      rfl

theorem cell22_2972318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_2972318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972318 prefixEnd_2972318 := by exact prefixLift 2972318
  have htrace : WordTrace (prefixWord ++ tailWord_2972318) baseStart_2972318 baseEnd_2972318 := by
    simpa [prefixWord, tailWord_2972318, baseEnd_2972318] using wordTrace_append hprefix tailTrace_2972318
  have hstable : (prefixWord ++ tailWord_2972318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972318).length < 2 ^ (prefixWord ++ tailWord_2972318).sum := by decide
  have hdescent : baseEnd_2972318 < baseStart_2972318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972461 : List Nat := [1, 5, 3, 2, 2, 1, 2, 2, 4]
def baseStart_2972461 : Nat := 118140960795 + 2972461 * 2 ^ 59
def prefixEnd_2972461 : Nat := 4983230072969 + 3 ^ 40 * 2972461 * 2
def baseEnd_2972461 : Nat := 339178048832044436970535

theorem tailTrace_2972461 : CollatzResearch.WordTrace tailWord_2972461 prefixEnd_2972461 339178048832044436970535 := by
  unfold tailWord_2972461
  simp only [CollatzResearch.WordTrace]
  refine ⟨108414559284288927767357237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72276372856192618511571491 108414559284288927767357237)
  ·
    refine ⟨10163864932902086978189741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108414559284288927767357237 10163864932902086978189741)
    ·
      refine ⟨3811449349838282616821153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10163864932902086978189741 3811449349838282616821153)
      ·
        refine ⟨2858587012378711962615865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3811449349838282616821153 2858587012378711962615865)
        ·
          refine ⟨2143940259284033971961899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2858587012378711962615865 2143940259284033971961899)
          ·
            refine ⟨3215910388926050957942849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2143940259284033971961899 3215910388926050957942849)
            ·
              refine ⟨2411932791694538218457137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3215910388926050957942849 2411932791694538218457137)
              ·
                refine ⟨1808949593770903663842853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2411932791694538218457137 1808949593770903663842853)
                ·
                  refine ⟨339178048832044436970535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1808949593770903663842853 339178048832044436970535)
                  ·
                    rfl

theorem cell22_2972461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_2972461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972461 prefixEnd_2972461 := by exact prefixLift 2972461
  have htrace : WordTrace (prefixWord ++ tailWord_2972461) baseStart_2972461 baseEnd_2972461 := by
    simpa [prefixWord, tailWord_2972461, baseEnd_2972461] using wordTrace_append hprefix tailTrace_2972461
  have hstable : (prefixWord ++ tailWord_2972461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972461).length < 2 ^ (prefixWord ++ tailWord_2972461).sum := by decide
  have hdescent : baseEnd_2972461 < baseStart_2972461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972464 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 3, 7]
def baseStart_2972464 : Nat := 118140960795 + 2972464 * 2 ^ 59
def prefixEnd_2972464 : Nat := 4983230072969 + 3 ^ 40 * 2972464 * 2
def baseEnd_2972464 : Nat := 1017535173457442303086595

theorem tailTrace_2972464 : CollatzResearch.WordTrace tailWord_2972464 prefixEnd_2972464 1017535173457442303086595 := by
  unfold tailWord_2972464
  simp only [CollatzResearch.WordTrace]
  refine ⟨54207334351639029639858223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72276445802185372853144297 54207334351639029639858223)
  ·
    refine ⟨81311001527458544459787335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54207334351639029639858223 81311001527458544459787335)
    ·
      refine ⟨121966502291187816689681003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81311001527458544459787335 121966502291187816689681003)
      ·
        refine ⟨182949753436781725034521505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121966502291187816689681003 182949753436781725034521505)
        ·
          refine ⟨137212315077586293775891129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182949753436781725034521505 137212315077586293775891129)
          ·
            refine ⟨102909236308189720331918347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137212315077586293775891129 102909236308189720331918347)
            ·
              refine ⟨154363854462284580497877521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102909236308189720331918347 154363854462284580497877521)
              ·
                refine ⟨115772890846713435373408141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154363854462284580497877521 115772890846713435373408141)
                ·
                  refine ⟨43414834067517538265028053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115772890846713435373408141 43414834067517538265028053)
                  ·
                    refine ⟨1017535173457442303086595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43414834067517538265028053 1017535173457442303086595)
                    ·
                      rfl

theorem cell22_2972464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_2972464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972464 prefixEnd_2972464 := by exact prefixLift 2972464
  have htrace : WordTrace (prefixWord ++ tailWord_2972464) baseStart_2972464 baseEnd_2972464 := by
    simpa [prefixWord, tailWord_2972464, baseEnd_2972464] using wordTrace_append hprefix tailTrace_2972464
  have hstable : (prefixWord ++ tailWord_2972464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972464).length < 2 ^ (prefixWord ++ tailWord_2972464).sum := by decide
  have hdescent : baseEnd_2972464 < baseStart_2972464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972496 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 3, 4]
def baseStart_2972496 : Nat := 118140960795 + 2972496 * 2 ^ 59
def prefixEnd_2972496 : Nat := 4983230072969 + 3 ^ 40 * 2972496 * 2
def baseEnd_2972496 : Nat := 1017546127711404886286497

theorem tailTrace_2972496 : CollatzResearch.WordTrace tailWord_2972496 prefixEnd_2972496 1017546127711404886286497 := by
  unfold tailWord_2972496
  simp only [CollatzResearch.WordTrace]
  refine ⟨54207917919581064372440671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72277223892774752496587561 54207917919581064372440671)
  ·
    refine ⟨81311876879371596558661007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54207917919581064372440671 81311876879371596558661007)
    ·
      refine ⟨121967815319057394837991511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81311876879371596558661007 121967815319057394837991511)
      ·
        refine ⟨182951722978586092256987267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121967815319057394837991511 182951722978586092256987267)
        ·
          refine ⟨274427584467879138385480901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182951722978586092256987267 274427584467879138385480901)
          ·
            refine ⟨51455172087727338447277669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 274427584467879138385480901 51455172087727338447277669)
            ·
              refine ⟨9647844766448875958864563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51455172087727338447277669 9647844766448875958864563)
              ·
                refine ⟨14471767149673313938296845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9647844766448875958864563 14471767149673313938296845)
                ·
                  refine ⟨5426912681127492726861317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14471767149673313938296845 5426912681127492726861317)
                  ·
                    refine ⟨1017546127711404886286497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5426912681127492726861317 1017546127711404886286497)
                    ·
                      rfl

theorem cell22_2972496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_2972496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972496 prefixEnd_2972496 := by exact prefixLift 2972496
  have htrace : WordTrace (prefixWord ++ tailWord_2972496) baseStart_2972496 baseEnd_2972496 := by
    simpa [prefixWord, tailWord_2972496, baseEnd_2972496] using wordTrace_append hprefix tailTrace_2972496
  have hstable : (prefixWord ++ tailWord_2972496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972496).length < 2 ^ (prefixWord ++ tailWord_2972496).sum := by decide
  have hdescent : baseEnd_2972496 < baseStart_2972496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972528 : List Nat := [2, 1, 1, 1, 4, 1, 4, 4, 4]
def baseStart_2972528 : Nat := 118140960795 + 2972528 * 2 ^ 59
def prefixEnd_2972528 : Nat := 4983230072969 + 3 ^ 40 * 2972528 * 2
def baseEnd_2972528 : Nat := 339185693988455823162133

theorem tailTrace_2972528 : CollatzResearch.WordTrace tailWord_2972528 prefixEnd_2972528 339185693988455823162133 := by
  unfold tailWord_2972528
  simp only [CollatzResearch.WordTrace]
  refine ⟨54208501487523099105023119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72278001983364132140030825 54208501487523099105023119)
  ·
    refine ⟨81312752231284648657534679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54208501487523099105023119 81312752231284648657534679)
    ·
      refine ⟨121969128346926972986302019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81312752231284648657534679 121969128346926972986302019)
      ·
        refine ⟨182953692520390459479453029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121969128346926972986302019 182953692520390459479453029)
        ·
          refine ⟨34303817347573211152397443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182953692520390459479453029 34303817347573211152397443)
          ·
            refine ⟨51455726021359816728596165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34303817347573211152397443 51455726021359816728596165)
            ·
              refine ⟨9647948629004965636611781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51455726021359816728596165 9647948629004965636611781)
              ·
                refine ⟨1808990367938431056864709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9647948629004965636611781 1808990367938431056864709)
                ·
                  refine ⟨339185693988455823162133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1808990367938431056864709 339185693988455823162133)
                  ·
                    rfl

theorem cell22_2972528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 4].length) (baseStart_2972528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972528 prefixEnd_2972528 := by exact prefixLift 2972528
  have htrace : WordTrace (prefixWord ++ tailWord_2972528) baseStart_2972528 baseEnd_2972528 := by
    simpa [prefixWord, tailWord_2972528, baseEnd_2972528] using wordTrace_append hprefix tailTrace_2972528
  have hstable : (prefixWord ++ tailWord_2972528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972528).length < 2 ^ (prefixWord ++ tailWord_2972528).sum := by decide
  have hdescent : baseEnd_2972528 < baseStart_2972528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972541 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_2972541 : Nat := 118140960795 + 2972541 * 2 ^ 59
def prefixEnd_2972541 : Nat := 4983230072969 + 3 ^ 40 * 2972541 * 2
def baseEnd_2972541 : Nat := 1017561532131039768911359

theorem tailTrace_2972541 : CollatzResearch.WordTrace tailWord_2972541 prefixEnd_2972541 1017561532131039768911359 := by
  unfold tailWord_2972541
  simp only [CollatzResearch.WordTrace]
  refine ⟨108417477123999101430269477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72278318082666067620179651 108417477123999101430269477)
  ·
    refine ⟨20328276960749831518175527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108417477123999101430269477 20328276960749831518175527)
    ·
      refine ⟨30492415441124747277263291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20328276960749831518175527 30492415441124747277263291)
      ·
        refine ⟨45738623161687120915894937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30492415441124747277263291 45738623161687120915894937)
        ·
          refine ⟨34303967371265340686921203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45738623161687120915894937 34303967371265340686921203)
          ·
            refine ⟨51455951056898011030381805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34303967371265340686921203 51455951056898011030381805)
            ·
              refine ⟨19295981646336754136393177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51455951056898011030381805 19295981646336754136393177)
              ·
                refine ⟨14471986234752565602294883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19295981646336754136393177 14471986234752565602294883)
                ·
                  refine ⟨21707979352128848403442325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14471986234752565602294883 21707979352128848403442325)
                  ·
                    refine ⟨1017561532131039768911359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21707979352128848403442325 1017561532131039768911359)
                    ·
                      rfl

theorem cell22_2972541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_2972541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972541 prefixEnd_2972541 := by exact prefixLift 2972541
  have htrace : WordTrace (prefixWord ++ tailWord_2972541) baseStart_2972541 baseEnd_2972541 := by
    simpa [prefixWord, tailWord_2972541, baseEnd_2972541] using wordTrace_append hprefix tailTrace_2972541
  have hstable : (prefixWord ++ tailWord_2972541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972541).length < 2 ^ (prefixWord ++ tailWord_2972541).sum := by decide
  have hdescent : baseEnd_2972541 < baseStart_2972541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972543 : List Nat := [1, 1, 2, 2, 1, 1, 4, 5, 2, 3]
def baseStart_2972543 : Nat := 118140960795 + 2972543 * 2 ^ 59
def prefixEnd_2972543 : Nat := 4983230072969 + 3 ^ 40 * 2972543 * 2
def baseEnd_2972543 : Nat := 1017562216771912430361353

theorem tailTrace_2972543 : CollatzResearch.WordTrace tailWord_2972543 prefixEnd_2972543 1017562216771912430361353 := by
  unfold tailWord_2972543
  simp only [CollatzResearch.WordTrace]
  refine ⟨108417550069991855771842283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72278366713327903847894855 108417550069991855771842283)
  ·
    refine ⟨162626325104987783657763425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108417550069991855771842283 162626325104987783657763425)
    ·
      refine ⟨121969743828740837743322569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162626325104987783657763425 121969743828740837743322569)
      ·
        refine ⟨91477307871555628307491927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121969743828740837743322569 91477307871555628307491927)
        ·
          refine ⟨137215961807333442461237891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91477307871555628307491927 137215961807333442461237891)
          ·
            refine ⟨205823942711000163691856837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137215961807333442461237891 205823942711000163691856837)
            ·
              refine ⟨38591989258312530692223157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205823942711000163691856837 38591989258312530692223157)
              ·
                refine ⟨3617998992966799752395921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38591989258312530692223157 3617998992966799752395921)
                ·
                  refine ⟨2713499244725099814296941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3617998992966799752395921 2713499244725099814296941)
                  ·
                    refine ⟨1017562216771912430361353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2713499244725099814296941 1017562216771912430361353)
                    ·
                      rfl

theorem cell22_2972543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 3].length) (baseStart_2972543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972543 prefixEnd_2972543 := by exact prefixLift 2972543
  have htrace : WordTrace (prefixWord ++ tailWord_2972543) baseStart_2972543 baseEnd_2972543 := by
    simpa [prefixWord, tailWord_2972543, baseEnd_2972543] using wordTrace_append hprefix tailTrace_2972543
  have hstable : (prefixWord ++ tailWord_2972543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972543).length < 2 ^ (prefixWord ++ tailWord_2972543).sum := by decide
  have hdescent : baseEnd_2972543 < baseStart_2972543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972598 : List Nat := [5, 1, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_2972598 : Nat := 118140960795 + 2972598 * 2 ^ 59
def prefixEnd_2972598 : Nat := 4983230072969 + 3 ^ 40 * 2972598 * 2
def baseEnd_2972598 : Nat := 1017581044395910620236185

theorem tailTrace_2972598 : CollatzResearch.WordTrace tailWord_2972598 prefixEnd_2972598 1017581044395910620236185 := by
  unfold tailWord_2972598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6776222255299537510318403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72279704056528400110062965 6776222255299537510318403)
  ·
    refine ⟨10164333382949306265477605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6776222255299537510318403 10164333382949306265477605)
    ·
      refine ⟨1905812509302994924777051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10164333382949306265477605 1905812509302994924777051)
      ·
        refine ⟨2858718763954492387165577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1905812509302994924777051 2858718763954492387165577)
        ·
          refine ⟨2144039072965869290374183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2858718763954492387165577 2144039072965869290374183)
          ·
            refine ⟨3216058609448803935561275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2144039072965869290374183 3216058609448803935561275)
            ·
              refine ⟨4824087914173205903341913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3216058609448803935561275 4824087914173205903341913)
              ·
                refine ⟨3618065935629904427506435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4824087914173205903341913 3618065935629904427506435)
                ·
                  refine ⟨5427098903444856641259653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3618065935629904427506435 5427098903444856641259653)
                  ·
                    refine ⟨1017581044395910620236185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5427098903444856641259653 1017581044395910620236185)
                    ·
                      rfl

theorem cell22_2972598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_2972598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972598 prefixEnd_2972598 := by exact prefixLift 2972598
  have htrace : WordTrace (prefixWord ++ tailWord_2972598) baseStart_2972598 baseEnd_2972598 := by
    simpa [prefixWord, tailWord_2972598, baseEnd_2972598] using wordTrace_append hprefix tailTrace_2972598
  have hstable : (prefixWord ++ tailWord_2972598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972598).length < 2 ^ (prefixWord ++ tailWord_2972598).sum := by decide
  have hdescent : baseEnd_2972598 < baseStart_2972598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972648 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 3, 4]
def baseStart_2972648 : Nat := 118140960795 + 2972648 * 2 ^ 59
def prefixEnd_2972648 : Nat := 4983230072969 + 3 ^ 40 * 2972648 * 2
def baseEnd_2972648 : Nat := 1017598160417727156486031

theorem tailTrace_2972648 : CollatzResearch.WordTrace tailWord_2972648 prefixEnd_2972648 1017598160417727156486031 := by
  unfold tailWord_2972648
  simp only [CollatzResearch.WordTrace]
  refine ⟨54210689867305729352207299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72280919823074305802943065 54210689867305729352207299)
  ·
    refine ⟨81316034800958594028310949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54210689867305729352207299 81316034800958594028310949)
    ·
      refine ⟨15246756525179736380308303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81316034800958594028310949 15246756525179736380308303)
      ·
        refine ⟨22870134787769604570462455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15246756525179736380308303 22870134787769604570462455)
        ·
          refine ⟨34305202181654406855693683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22870134787769604570462455 34305202181654406855693683)
          ·
            refine ⟨51457803272481610283540525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34305202181654406855693683 51457803272481610283540525)
            ·
              refine ⟨19296676227180603856327697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51457803272481610283540525 19296676227180603856327697)
              ·
                refine ⟨14472507170385452892245773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19296676227180603856327697 14472507170385452892245773)
                ·
                  refine ⟨5427190188894544834592165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14472507170385452892245773 5427190188894544834592165)
                  ·
                    refine ⟨1017598160417727156486031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5427190188894544834592165 1017598160417727156486031)
                    ·
                      rfl

theorem cell22_2972648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_2972648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972648 prefixEnd_2972648 := by exact prefixLift 2972648
  have htrace : WordTrace (prefixWord ++ tailWord_2972648) baseStart_2972648 baseEnd_2972648 := by
    simpa [prefixWord, tailWord_2972648, baseEnd_2972648] using wordTrace_append hprefix tailTrace_2972648
  have hstable : (prefixWord ++ tailWord_2972648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972648).length < 2 ^ (prefixWord ++ tailWord_2972648).sum := by decide
  have hdescent : baseEnd_2972648 < baseStart_2972648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972680 : List Nat := [2, 1, 3, 2, 1, 3, 1, 5, 4]
def baseStart_2972680 : Nat := 118140960795 + 2972680 * 2 ^ 59
def prefixEnd_2972680 : Nat := 4983230072969 + 3 ^ 40 * 2972680 * 2
def baseEnd_2972680 : Nat := 339203038223896579895311

theorem tailTrace_2972680 : CollatzResearch.WordTrace tailWord_2972680 prefixEnd_2972680 339203038223896579895311 := by
  unfold tailWord_2972680
  simp only [CollatzResearch.WordTrace]
  refine ⟨54211273435247764084789747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72281697913663685446386329 54211273435247764084789747)
  ·
    refine ⟨81316910152871646127184621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54211273435247764084789747 81316910152871646127184621)
    ·
      refine ⟨30493841307326867297694233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81316910152871646127184621 30493841307326867297694233)
      ·
        refine ⟨22870380980495150473270675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30493841307326867297694233 22870380980495150473270675)
        ·
          refine ⟨34305571470742725709906013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22870380980495150473270675 34305571470742725709906013)
          ·
            refine ⟨12864589301528522141214755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34305571470742725709906013 12864589301528522141214755)
            ·
              refine ⟨19296883952292783211822133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12864589301528522141214755 19296883952292783211822133)
              ·
                refine ⟨1809082870527448426108325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19296883952292783211822133 1809082870527448426108325)
                ·
                  refine ⟨339203038223896579895311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1809082870527448426108325 339203038223896579895311)
                  ·
                    rfl

theorem cell22_2972680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 4].length) (baseStart_2972680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972680 prefixEnd_2972680 := by exact prefixLift 2972680
  have htrace : WordTrace (prefixWord ++ tailWord_2972680) baseStart_2972680 baseEnd_2972680 := by
    simpa [prefixWord, tailWord_2972680, baseEnd_2972680] using wordTrace_append hprefix tailTrace_2972680
  have hstable : (prefixWord ++ tailWord_2972680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972680).length < 2 ^ (prefixWord ++ tailWord_2972680).sum := by decide
  have hdescent : baseEnd_2972680 < baseStart_2972680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972682 : List Nat := [3, 1, 2, 2, 3, 1, 4, 1, 1, 4]
def baseStart_2972682 : Nat := 118140960795 + 2972682 * 2 ^ 59
def prefixEnd_2972682 : Nat := 4983230072969 + 3 ^ 40 * 2972682 * 2
def baseEnd_2972682 : Nat := 1017609799312562401135927

theorem tailTrace_2972682 : CollatzResearch.WordTrace tailWord_2972682 prefixEnd_2972682 1017609799312562401135927 := by
  unfold tailWord_2972682
  simp only [CollatzResearch.WordTrace]
  refine ⟨27105654954122070627788075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72281746544325521674101533 27105654954122070627788075)
  ·
    refine ⟨40658482431183105941682113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27105654954122070627788075 40658482431183105941682113)
    ·
      refine ⟨30493861823387329456261585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40658482431183105941682113 30493861823387329456261585)
      ·
        refine ⟨22870396367540497092196189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30493861823387329456261585 22870396367540497092196189)
        ·
          refine ⟨8576398637827686409573571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22870396367540497092196189 8576398637827686409573571)
          ·
            refine ⟨12864597956741529614360357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8576398637827686409573571 12864597956741529614360357)
            ·
              refine ⟨2412112116889036802692567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12864597956741529614360357 2412112116889036802692567)
              ·
                refine ⟨3618168175333555204038851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2412112116889036802692567 3618168175333555204038851)
                ·
                  refine ⟨5427252263000332806058277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3618168175333555204038851 5427252263000332806058277)
                  ·
                    refine ⟨1017609799312562401135927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5427252263000332806058277 1017609799312562401135927)
                    ·
                      rfl

theorem cell22_2972682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_2972682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972682 prefixEnd_2972682 := by exact prefixLift 2972682
  have htrace : WordTrace (prefixWord ++ tailWord_2972682) baseStart_2972682 baseEnd_2972682 := by
    simpa [prefixWord, tailWord_2972682, baseEnd_2972682] using wordTrace_append hprefix tailTrace_2972682
  have hstable : (prefixWord ++ tailWord_2972682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972682).length < 2 ^ (prefixWord ++ tailWord_2972682).sum := by decide
  have hdescent : baseEnd_2972682 < baseStart_2972682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972742 : List Nat := [6, 1, 1, 1, 1, 4, 8]
def baseStart_2972742 : Nat := 118140960795 + 2972742 * 2 ^ 59
def prefixEnd_2972742 : Nat := 4983230072969 + 3 ^ 40 * 2972742 * 2
def baseEnd_2972742 : Nat := 37690012538471934986509

theorem tailTrace_2972742 : CollatzResearch.WordTrace tailWord_2972742 prefixEnd_2972742 37690012538471934986509 := by
  unfold tailWord_2972742
  simp only [CollatzResearch.WordTrace]
  refine ⟨3388275256133466023698015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72283205464180608505557653 3388275256133466023698015)
  ·
    refine ⟨5082412884200199035547023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3388275256133466023698015 5082412884200199035547023)
    ·
      refine ⟨7623619326300298553320535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5082412884200199035547023 7623619326300298553320535)
      ·
        refine ⟨11435428989450447829980803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7623619326300298553320535 11435428989450447829980803)
        ·
          refine ⟨17153143484175671744971205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11435428989450447829980803 17153143484175671744971205)
          ·
            refine ⟨3216214403282938452182101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17153143484175671744971205 3216214403282938452182101)
            ·
              refine ⟨37690012538471934986509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3216214403282938452182101 37690012538471934986509)
              ·
                rfl

theorem cell22_2972742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 8].length) (baseStart_2972742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972742 prefixEnd_2972742 := by exact prefixLift 2972742
  have htrace : WordTrace (prefixWord ++ tailWord_2972742) baseStart_2972742 baseEnd_2972742 := by
    simpa [prefixWord, tailWord_2972742, baseEnd_2972742] using wordTrace_append hprefix tailTrace_2972742
  have hstable : (prefixWord ++ tailWord_2972742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972742).length < 2 ^ (prefixWord ++ tailWord_2972742).sum := by decide
  have hdescent : baseEnd_2972742 < baseStart_2972742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972753 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 7]
def baseStart_2972753 : Nat := 118140960795 + 2972753 * 2 ^ 59
def prefixEnd_2972753 : Nat := 4983230072969 + 3 ^ 40 * 2972753 * 2
def baseEnd_2972753 : Nat := 339211368021180627536903

theorem tailTrace_2972753 : CollatzResearch.WordTrace tailWord_2972753 prefixEnd_2972753 339211368021180627536903 := by
  unfold tailWord_2972753
  simp only [CollatzResearch.WordTrace]
  refine ⟨108425209399231061636986913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72283472932820707757991275 108425209399231061636986913)
  ·
    refine ⟨81318907049423296227740185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108425209399231061636986913 81318907049423296227740185)
    ·
      refine ⟨60989180287067472170805139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81318907049423296227740185 60989180287067472170805139)
      ·
        refine ⟨91483770430601208256207709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60989180287067472170805139 91483770430601208256207709)
        ·
          refine ⟨34306413911475453096077891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91483770430601208256207709 34306413911475453096077891)
          ·
            refine ⟨51459620867213179644116837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34306413911475453096077891 51459620867213179644116837)
            ·
              refine ⟨9648678912602471183271907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51459620867213179644116837 9648678912602471183271907)
              ·
                refine ⟨14473018368903706774907861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9648678912602471183271907 14473018368903706774907861)
                ·
                  refine ⟨339211368021180627536903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14473018368903706774907861 339211368021180627536903)
                  ·
                    rfl

theorem cell22_2972753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 7].length) (baseStart_2972753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972753 prefixEnd_2972753 := by exact prefixLift 2972753
  have htrace : WordTrace (prefixWord ++ tailWord_2972753) baseStart_2972753 baseEnd_2972753 := by
    simpa [prefixWord, tailWord_2972753, baseEnd_2972753] using wordTrace_append hprefix tailTrace_2972753
  have hstable : (prefixWord ++ tailWord_2972753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972753).length < 2 ^ (prefixWord ++ tailWord_2972753).sum := by decide
  have hdescent : baseEnd_2972753 < baseStart_2972753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972768 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 1, 7]
def baseStart_2972768 : Nat := 118140960795 + 2972768 * 2 ^ 59
def prefixEnd_2972768 : Nat := 4983230072969 + 3 ^ 40 * 2972768 * 2
def baseEnd_2972768 : Nat := 1017639238870086843485663

theorem tailTrace_2972768 : CollatzResearch.WordTrace tailWord_2972768 prefixEnd_2972768 1017639238870086843485663 := by
  unfold tailWord_2972768
  simp only [CollatzResearch.WordTrace]
  refine ⟨54212878247088359599391479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72283837662784479465855305 54212878247088359599391479)
  ·
    refine ⟨81319317370632539399087219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54212878247088359599391479 81319317370632539399087219)
    ·
      refine ⟨121978976055948809098630829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81319317370632539399087219 121978976055948809098630829)
      ·
        refine ⟨45742116020980803411986561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121978976055948809098630829 45742116020980803411986561)
        ·
          refine ⟨34306587015735602558989921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45742116020980803411986561 34306587015735602558989921)
          ·
            refine ⟨25729940261801701919242441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34306587015735602558989921 25729940261801701919242441)
            ·
              refine ⟨19297455196351276439431831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25729940261801701919242441 19297455196351276439431831)
              ·
                refine ⟨28946182794526914659147747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19297455196351276439431831 28946182794526914659147747)
                ·
                  refine ⟨43419274191790371988721621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28946182794526914659147747 43419274191790371988721621)
                  ·
                    refine ⟨1017639238870086843485663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43419274191790371988721621 1017639238870086843485663)
                    ·
                      rfl

theorem cell22_2972768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_2972768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972768 prefixEnd_2972768 := by exact prefixLift 2972768
  have htrace : WordTrace (prefixWord ++ tailWord_2972768) baseStart_2972768 baseEnd_2972768 := by
    simpa [prefixWord, tailWord_2972768, baseEnd_2972768] using wordTrace_append hprefix tailTrace_2972768
  have hstable : (prefixWord ++ tailWord_2972768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972768).length < 2 ^ (prefixWord ++ tailWord_2972768).sum := by decide
  have hdescent : baseEnd_2972768 < baseStart_2972768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972800 : List Nat := [2, 1, 1, 2, 1, 3, 2, 5, 1, 4]
def baseStart_2972800 : Nat := 118140960795 + 2972800 * 2 ^ 59
def prefixEnd_2972800 : Nat := 4983230072969 + 3 ^ 40 * 2972800 * 2
def baseEnd_2972800 : Nat := 1017650193124049426685565

theorem tailTrace_2972800 : CollatzResearch.WordTrace tailWord_2972800 prefixEnd_2972800 1017650193124049426685565 := by
  unfold tailWord_2972800
  simp only [CollatzResearch.WordTrace]
  refine ⟨54213461815030394331973927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72284615753373859109298569 54213461815030394331973927)
  ·
    refine ⟨81320192722545591497960891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54213461815030394331973927 81320192722545591497960891)
    ·
      refine ⟨121980289083818387246941337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81320192722545591497960891 121980289083818387246941337)
      ·
        refine ⟨91485216812863790435206003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121980289083818387246941337 91485216812863790435206003)
        ·
          refine ⟨137227825219295685652809005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91485216812863790435206003 137227825219295685652809005)
          ·
            refine ⟨51460434457235882119803377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137227825219295685652809005 51460434457235882119803377)
            ·
              refine ⟨38595325842926911589852533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51460434457235882119803377 38595325842926911589852533)
              ·
                refine ⟨3618311797774397961548675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38595325842926911589852533 3618311797774397961548675)
                ·
                  refine ⟨5427467696661596942323013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3618311797774397961548675 5427467696661596942323013)
                  ·
                    refine ⟨1017650193124049426685565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5427467696661596942323013 1017650193124049426685565)
                    ·
                      rfl

theorem cell22_2972800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 1, 4].length) (baseStart_2972800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972800 prefixEnd_2972800 := by exact prefixLift 2972800
  have htrace : WordTrace (prefixWord ++ tailWord_2972800) baseStart_2972800 baseEnd_2972800 := by
    simpa [prefixWord, tailWord_2972800, baseEnd_2972800] using wordTrace_append hprefix tailTrace_2972800
  have hstable : (prefixWord ++ tailWord_2972800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972800).length < 2 ^ (prefixWord ++ tailWord_2972800).sum := by decide
  have hdescent : baseEnd_2972800 < baseStart_2972800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972808 : List Nat := [2, 1, 3, 4, 2, 2, 2, 2, 1, 3]
def baseStart_2972808 : Nat := 118140960795 + 2972808 * 2 ^ 59
def prefixEnd_2972808 : Nat := 4983230072969 + 3 ^ 40 * 2972808 * 2
def baseEnd_2972808 : Nat := 1017652931687540072485541

theorem tailTrace_2972808 : CollatzResearch.WordTrace tailWord_2972808 prefixEnd_2972808 1017652931687540072485541 := by
  unfold tailWord_2972808
  simp only [CollatzResearch.WordTrace]
  refine ⟨54213607707015903015119539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72284810276021204020159385 54213607707015903015119539)
  ·
    refine ⟨81320411560523854522679309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54213607707015903015119539 81320411560523854522679309)
    ·
      refine ⟨30495154335196445446004741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81320411560523854522679309 30495154335196445446004741)
      ·
        refine ⟨5717841437849333521125889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30495154335196445446004741 5717841437849333521125889)
        ·
          refine ⟨4288381078387000140844417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5717841437849333521125889 4288381078387000140844417)
          ·
            refine ⟨3216285808790250105633313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4288381078387000140844417 3216285808790250105633313)
            ·
              refine ⟨2412214356592687579224985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3216285808790250105633313 2412214356592687579224985)
              ·
                refine ⟨1809160767444515684418739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2412214356592687579224985 1809160767444515684418739)
                ·
                  refine ⟨2713741151166773526628109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1809160767444515684418739 2713741151166773526628109)
                  ·
                    refine ⟨1017652931687540072485541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2713741151166773526628109 1017652931687540072485541)
                    ·
                      rfl

theorem cell22_2972808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_2972808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972808 prefixEnd_2972808 := by exact prefixLift 2972808
  have htrace : WordTrace (prefixWord ++ tailWord_2972808) baseStart_2972808 baseEnd_2972808 := by
    simpa [prefixWord, tailWord_2972808, baseEnd_2972808] using wordTrace_append hprefix tailTrace_2972808
  have hstable : (prefixWord ++ tailWord_2972808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972808).length < 2 ^ (prefixWord ++ tailWord_2972808).sum := by decide
  have hdescent : baseEnd_2972808 < baseStart_2972808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972849 : List Nat := [1, 2, 2, 5, 1, 2, 2, 3, 4]
def baseStart_2972849 : Nat := 118140960795 + 2972849 * 2 ^ 59
def prefixEnd_2972849 : Nat := 4983230072969 + 3 ^ 40 * 2972849 * 2
def baseEnd_2972849 : Nat := 339222322275143210736805

theorem tailTrace_2972849 : CollatzResearch.WordTrace tailWord_2972849 prefixEnd_2972849 339222322275143210736805 := by
  unfold tailWord_2972849
  simp only [CollatzResearch.WordTrace]
  refine ⟨108428710806883270032481601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72285807204588846688321067 108428710806883270032481601)
  ·
    refine ⟨81321533105162452524361201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108428710806883270032481601 81321533105162452524361201)
    ·
      refine ⟨60991149828871839393270901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81321533105162452524361201 60991149828871839393270901)
      ·
        refine ⟨5717920296456734943119147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60991149828871839393270901 5717920296456734943119147)
        ·
          refine ⟨8576880444685102414678721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5717920296456734943119147 8576880444685102414678721)
          ·
            refine ⟨6432660333513826811009041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8576880444685102414678721 6432660333513826811009041)
            ·
              refine ⟨4824495250135370108256781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6432660333513826811009041 4824495250135370108256781)
              ·
                refine ⟨1809185718800763790596293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4824495250135370108256781 1809185718800763790596293)
                ·
                  refine ⟨339222322275143210736805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1809185718800763790596293 339222322275143210736805)
                  ·
                    rfl

theorem cell22_2972849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 4].length) (baseStart_2972849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972849 prefixEnd_2972849 := by exact prefixLift 2972849
  have htrace : WordTrace (prefixWord ++ tailWord_2972849) baseStart_2972849 baseEnd_2972849 := by
    simpa [prefixWord, tailWord_2972849, baseEnd_2972849] using wordTrace_append hprefix tailTrace_2972849
  have hstable : (prefixWord ++ tailWord_2972849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972849).length < 2 ^ (prefixWord ++ tailWord_2972849).sum := by decide
  have hdescent : baseEnd_2972849 < baseStart_2972849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972860 : List Nat := [2, 2, 2, 3, 2, 2, 9]
def baseStart_2972860 : Nat := 118140960795 + 2972860 * 2 ^ 59
def prefixEnd_2972860 : Nat := 4983230072969 + 3 ^ 40 * 2972860 * 2
def baseEnd_2972860 : Nat := 37691508605564047043903

theorem tailTrace_2972860 : CollatzResearch.WordTrace tailWord_2972860 prefixEnd_2972860 37691508605564047043903 := by
  unfold tailWord_2972860
  simp only [CollatzResearch.WordTrace]
  refine ⟨54214556004921709455566017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72286074673228945940754689 54214556004921709455566017)
  ·
    refine ⟨40660917003691282091674513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54214556004921709455566017 40660917003691282091674513)
    ·
      refine ⟨30495687752768461568755885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40660917003691282091674513 30495687752768461568755885)
      ·
        refine ⟨11435882907288173088283457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30495687752768461568755885 11435882907288173088283457)
        ·
          refine ⟨8576912180466129816212593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11435882907288173088283457 8576912180466129816212593)
          ·
            refine ⟨6432684135349597362159445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8576912180466129816212593 6432684135349597362159445)
            ·
              refine ⟨37691508605564047043903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6432684135349597362159445 37691508605564047043903)
              ·
                rfl

theorem cell22_2972860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 9].length) (baseStart_2972860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972860 prefixEnd_2972860 := by exact prefixLift 2972860
  have htrace : WordTrace (prefixWord ++ tailWord_2972860) baseStart_2972860 baseEnd_2972860 := by
    simpa [prefixWord, tailWord_2972860, baseEnd_2972860] using wordTrace_append hprefix tailTrace_2972860
  have hstable : (prefixWord ++ tailWord_2972860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972860).length < 2 ^ (prefixWord ++ tailWord_2972860).sum := by decide
  have hdescent : baseEnd_2972860 < baseStart_2972860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972866 : List Nat := [3, 5, 1, 1, 2, 1, 2, 1, 6]
def baseStart_2972866 : Nat := 118140960795 + 2972866 * 2 ^ 59
def prefixEnd_2972866 : Nat := 4983230072969 + 3 ^ 40 * 2972866 * 2
def baseEnd_2972866 : Nat := 339224262090949084845121

theorem tailTrace_2972866 : CollatzResearch.WordTrace tailWord_2972866 prefixEnd_2972866 339224262090949084845121 := by
  unfold tailWord_2972866
  simp only [CollatzResearch.WordTrace]
  refine ⟨27107332711955420483962613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72286220565214454623900301 27107332711955420483962613)
  ·
    refine ⟨2541312441745820670371495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27107332711955420483962613 2541312441745820670371495)
    ·
      refine ⟨3811968662618731005557243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2541312441745820670371495 3811968662618731005557243)
      ·
        refine ⟨5717952993928096508335865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3811968662618731005557243 5717952993928096508335865)
        ·
          refine ⟨4288464745446072381251899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5717952993928096508335865 4288464745446072381251899)
          ·
            refine ⟨6432697118169108571877849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4288464745446072381251899 6432697118169108571877849)
            ·
              refine ⟨4824522838626831428908387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6432697118169108571877849 4824522838626831428908387)
              ·
                refine ⟨7236784257940247143362581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4824522838626831428908387 7236784257940247143362581)
                ·
                  refine ⟨339224262090949084845121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7236784257940247143362581 339224262090949084845121)
                  ·
                    rfl

theorem cell22_2972866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_2972866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972866 prefixEnd_2972866 := by exact prefixLift 2972866
  have htrace : WordTrace (prefixWord ++ tailWord_2972866) baseStart_2972866 baseEnd_2972866 := by
    simpa [prefixWord, tailWord_2972866, baseEnd_2972866] using wordTrace_append hprefix tailTrace_2972866
  have hstable : (prefixWord ++ tailWord_2972866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972866).length < 2 ^ (prefixWord ++ tailWord_2972866).sum := by decide
  have hdescent : baseEnd_2972866 < baseStart_2972866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972926 : List Nat := [4, 2, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_2972926 : Nat := 118140960795 + 2972926 * 2 ^ 59
def prefixEnd_2972926 : Nat := 4983230072969 + 3 ^ 40 * 2972926 * 2
def baseEnd_2972926 : Nat := 1017693325499027098035179

theorem tailTrace_2972926 : CollatzResearch.WordTrace tailWord_2972926 prefixEnd_2972926 1017693325499027098035179 := by
  unfold tailWord_2972926
  simp only [CollatzResearch.WordTrace]
  refine ⟨13553939903450539022879329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72287679485069541455356421 13553939903450539022879329)
  ·
    refine ⟨10165454927587904267159497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13553939903450539022879329 10165454927587904267159497)
    ·
      refine ⟨7624091195690928200369623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10165454927587904267159497 7624091195690928200369623)
      ·
        refine ⟨11436136793536392300554435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7624091195690928200369623 11436136793536392300554435)
        ·
          refine ⟨17154205190304588450831653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11436136793536392300554435 17154205190304588450831653)
          ·
            refine ⟨3216413473182110334530935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17154205190304588450831653 3216413473182110334530935)
            ·
              refine ⟨4824620209773165501796403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3216413473182110334530935 4824620209773165501796403)
              ·
                refine ⟨7236930314659748252694605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4824620209773165501796403 7236930314659748252694605)
                ·
                  refine ⟨2713848867997405594760477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7236930314659748252694605 2713848867997405594760477)
                  ·
                    refine ⟨1017693325499027098035179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2713848867997405594760477 1017693325499027098035179)
                    ·
                      rfl

theorem cell22_2972926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_2972926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972926 prefixEnd_2972926 := by exact prefixLift 2972926
  have htrace : WordTrace (prefixWord ++ tailWord_2972926) baseStart_2972926 baseEnd_2972926 := by
    simpa [prefixWord, tailWord_2972926, baseEnd_2972926] using wordTrace_append hprefix tailTrace_2972926
  have hstable : (prefixWord ++ tailWord_2972926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972926).length < 2 ^ (prefixWord ++ tailWord_2972926).sum := by decide
  have hdescent : baseEnd_2972926 < baseStart_2972926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972939 : List Nat := [1, 1, 1, 1, 5, 5, 2, 1, 5]
def baseStart_2972939 : Nat := 118140960795 + 2972939 * 2 ^ 59
def prefixEnd_2972939 : Nat := 4983230072969 + 3 ^ 40 * 2972939 * 2
def baseEnd_2972939 : Nat := 339232591888233132486713

theorem tailTrace_2972939 : CollatzResearch.WordTrace tailWord_2972939 prefixEnd_2972939 339232591888233132486713 := by
  unfold tailWord_2972939
  simp only [CollatzResearch.WordTrace]
  refine ⟨108431993376557215403257871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72287995584371476935505247 108431993376557215403257871)
  ·
    refine ⟨162647990064835823104886807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108431993376557215403257871 162647990064835823104886807)
    ·
      refine ⟨243971985097253734657330211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162647990064835823104886807 243971985097253734657330211)
      ·
        refine ⟨365957977645880601985995317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243971985097253734657330211 365957977645880601985995317)
        ·
          refine ⟨34308560404301306436187061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 365957977645880601985995317 34308560404301306436187061)
          ·
            refine ⟨3216427537903247478392537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34308560404301306436187061 3216427537903247478392537)
            ·
              refine ⟨2412320653427435608794403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3216427537903247478392537 2412320653427435608794403)
              ·
                refine ⟨3618480980141153413191605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2412320653427435608794403 3618480980141153413191605)
                ·
                  refine ⟨339232591888233132486713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3618480980141153413191605 339232591888233132486713)
                  ·
                    rfl

theorem cell22_2972939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 5].length) (baseStart_2972939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972939 prefixEnd_2972939 := by exact prefixLift 2972939
  have htrace : WordTrace (prefixWord ++ tailWord_2972939) baseStart_2972939 baseEnd_2972939 := by
    simpa [prefixWord, tailWord_2972939, baseEnd_2972939] using wordTrace_append hprefix tailTrace_2972939
  have hstable : (prefixWord ++ tailWord_2972939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972939).length < 2 ^ (prefixWord ++ tailWord_2972939).sum := by decide
  have hdescent : baseEnd_2972939 < baseStart_2972939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972952 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 3, 4]
def baseStart_2972952 : Nat := 118140960795 + 2972952 * 2 ^ 59
def prefixEnd_2972952 : Nat := 4983230072969 + 3 ^ 40 * 2972952 * 2
def baseEnd_2972952 : Nat := 1017702225830371696885099

theorem tailTrace_2972952 : CollatzResearch.WordTrace tailWord_2972952 prefixEnd_2972952 1017702225830371696885099 := by
  unfold tailWord_2972952
  simp only [CollatzResearch.WordTrace]
  refine ⟨54216233762755059311740555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72288311683673412415654073 54216233762755059311740555)
  ·
    refine ⟨81324350644132588967610833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54216233762755059311740555 81324350644132588967610833)
    ·
      refine ⟨60993262983099441725708125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81324350644132588967610833 60993262983099441725708125)
      ·
        refine ⟨22872473618662290647140547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60993262983099441725708125 22872473618662290647140547)
        ·
          refine ⟨34308710427993435970710821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22872473618662290647140547 34308710427993435970710821)
          ·
            refine ⟨6432883205248769244508279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34308710427993435970710821 6432883205248769244508279)
            ·
              refine ⟨9649324807873153866762419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6432883205248769244508279 9649324807873153866762419)
              ·
                refine ⟨14473987211809730800143629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9649324807873153866762419 14473987211809730800143629)
                ·
                  refine ⟨5427745204428649050053861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14473987211809730800143629 5427745204428649050053861)
                  ·
                    refine ⟨1017702225830371696885099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5427745204428649050053861 1017702225830371696885099)
                    ·
                      rfl

theorem cell22_2972952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_2972952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972952 prefixEnd_2972952 := by exact prefixLift 2972952
  have htrace : WordTrace (prefixWord ++ tailWord_2972952) baseStart_2972952 baseEnd_2972952 := by
    simpa [prefixWord, tailWord_2972952, baseEnd_2972952] using wordTrace_append hprefix tailTrace_2972952
  have hstable : (prefixWord ++ tailWord_2972952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972952).length < 2 ^ (prefixWord ++ tailWord_2972952).sum := by decide
  have hdescent : baseEnd_2972952 < baseStart_2972952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972999 : List Nat := [1, 1, 4, 1, 2, 3, 2, 3, 2, 3]
def baseStart_2972999 : Nat := 118140960795 + 2972999 * 2 ^ 59
def prefixEnd_2972999 : Nat := 4983230072969 + 3 ^ 40 * 2972999 * 2
def baseEnd_2972999 : Nat := 1017718314890879240959955

theorem tailTrace_2972999 : CollatzResearch.WordTrace tailWord_2972999 prefixEnd_2972999 1017718314890879240959955 := by
  unfold tailWord_2972999
  simp only [CollatzResearch.WordTrace]
  refine ⟨108434181756339845650442051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72289454504226563766961367 108434181756339845650442051)
  ·
    refine ⟨162651272634509768475663077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108434181756339845650442051 162651272634509768475663077)
    ·
      refine ⟨30497113618970581589186827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162651272634509768475663077 30497113618970581589186827)
      ·
        refine ⟨45745670428455872383780241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30497113618970581589186827 45745670428455872383780241)
        ·
          refine ⟨34309252821341904287835181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45745670428455872383780241 34309252821341904287835181)
          ·
            refine ⟨12865969808003214107938193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34309252821341904287835181 12865969808003214107938193)
            ·
              refine ⟨9649477356002410580953645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12865969808003214107938193 9649477356002410580953645)
              ·
                refine ⟨3618554008500903967857617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9649477356002410580953645 3618554008500903967857617)
                ·
                  refine ⟨2713915506375677975893213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3618554008500903967857617 2713915506375677975893213)
                  ·
                    refine ⟨1017718314890879240959955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2713915506375677975893213 1017718314890879240959955)
                    ·
                      rfl

theorem cell22_2972999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_2972999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2972999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2972999 prefixEnd_2972999 := by exact prefixLift 2972999
  have htrace : WordTrace (prefixWord ++ tailWord_2972999) baseStart_2972999 baseEnd_2972999 := by
    simpa [prefixWord, tailWord_2972999, baseEnd_2972999] using wordTrace_append hprefix tailTrace_2972999
  have hstable : (prefixWord ++ tailWord_2972999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972999).length < 2 ^ (prefixWord ++ tailWord_2972999).sum := by decide
  have hdescent : baseEnd_2972999 < baseStart_2972999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973134 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 6, 3]
def baseStart_2973134 : Nat := 118140960795 + 2973134 * 2 ^ 59
def prefixEnd_2973134 : Nat := 4983230072969 + 3 ^ 40 * 2973134 * 2
def baseEnd_2973134 : Nat := 1017764528149783888834541

theorem tailTrace_2973134 : CollatzResearch.WordTrace tailWord_2973134 prefixEnd_2973134 1017764528149783888834541 := by
  unfold tailWord_2973134
  simp only [CollatzResearch.WordTrace]
  refine ⟨13554888201356345463325807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72292737073900509137737637 13554888201356345463325807)
  ·
    refine ⟨20332332302034518194988711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13554888201356345463325807 20332332302034518194988711)
    ·
      refine ⟨30498498453051777292483067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20332332302034518194988711 30498498453051777292483067)
      ·
        refine ⟨45747747679577665938724601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30498498453051777292483067 45747747679577665938724601)
        ·
          refine ⟨34310810759683249454043451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45747747679577665938724601 34310810759683249454043451)
          ·
            refine ⟨51466216139524874181065177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34310810759683249454043451 51466216139524874181065177)
            ·
              refine ⟨38599662104643655635798883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51466216139524874181065177 38599662104643655635798883)
              ·
                refine ⟨57899493156965483453698325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38599662104643655635798883 57899493156965483453698325)
                ·
                  refine ⟨2714038741732757036892109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57899493156965483453698325 2714038741732757036892109)
                  ·
                    refine ⟨1017764528149783888834541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2714038741732757036892109 1017764528149783888834541)
                    ·
                      rfl

theorem cell22_2973134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_2973134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973134 prefixEnd_2973134 := by exact prefixLift 2973134
  have htrace : WordTrace (prefixWord ++ tailWord_2973134) baseStart_2973134 baseEnd_2973134 := by
    simpa [prefixWord, tailWord_2973134, baseEnd_2973134] using wordTrace_append hprefix tailTrace_2973134
  have hstable : (prefixWord ++ tailWord_2973134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973134).length < 2 ^ (prefixWord ++ tailWord_2973134).sum := by decide
  have hdescent : baseEnd_2973134 < baseStart_2973134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973151 : List Nat := [1, 1, 2, 3, 3, 1, 4, 2, 2, 3]
def baseStart_2973151 : Nat := 118140960795 + 2973151 * 2 ^ 59
def prefixEnd_2973151 : Nat := 4983230072969 + 3 ^ 40 * 2973151 * 2
def baseEnd_2973151 : Nat := 1017770347597201511159489

theorem tailTrace_2973151 : CollatzResearch.WordTrace tailWord_2973151 prefixEnd_2973151 1017770347597201511159489 := by
  unfold tailWord_2973151
  simp only [CollatzResearch.WordTrace]
  refine ⟨108439725651789175609975307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72293150434526117073316871 108439725651789175609975307)
  ·
    refine ⟨162659588477683763414962961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108439725651789175609975307 162659588477683763414962961)
    ·
      refine ⟨121994691358262822561222221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162659588477683763414962961 121994691358262822561222221)
      ·
        refine ⟨45748009259348558460458333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121994691358262822561222221 45748009259348558460458333)
        ·
          refine ⟨17155503472255709422671875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45748009259348558460458333 17155503472255709422671875)
          ·
            refine ⟨25733255208383564134007813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17155503472255709422671875 25733255208383564134007813)
            ·
              refine ⟨4824985351571918275126465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25733255208383564134007813 4824985351571918275126465)
              ·
                refine ⟨3618739013678938706344849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4824985351571918275126465 3618739013678938706344849)
                ·
                  refine ⟨2714054260259204029758637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3618739013678938706344849 2714054260259204029758637)
                  ·
                    refine ⟨1017770347597201511159489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2714054260259204029758637 1017770347597201511159489)
                    ·
                      rfl

theorem cell22_2973151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 3].length) (baseStart_2973151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973151 prefixEnd_2973151 := by exact prefixLift 2973151
  have htrace : WordTrace (prefixWord ++ tailWord_2973151) baseStart_2973151 baseEnd_2973151 := by
    simpa [prefixWord, tailWord_2973151, baseEnd_2973151] using wordTrace_append hprefix tailTrace_2973151
  have hstable : (prefixWord ++ tailWord_2973151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973151).length < 2 ^ (prefixWord ++ tailWord_2973151).sum := by decide
  have hdescent : baseEnd_2973151 < baseStart_2973151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973153 : List Nat := [1, 2, 3, 1, 2, 5, 2, 2, 4]
def baseStart_2973153 : Nat := 118140960795 + 2973153 * 2 ^ 59
def prefixEnd_2973153 : Nat := 4983230072969 + 3 ^ 40 * 2973153 * 2
def baseEnd_2973153 : Nat := 339257010746024724203161

theorem tailTrace_2973153 : CollatzResearch.WordTrace tailWord_2973153 prefixEnd_2973153 339257010746024724203161 := by
  unfold tailWord_2973153
  simp only [CollatzResearch.WordTrace]
  refine ⟨108439798597781929951548113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72293199065187953301032075 108439798597781929951548113)
  ·
    refine ⟨81329848948336447463661085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108439798597781929951548113 81329848948336447463661085)
    ·
      refine ⟨30498693355626167798872907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81329848948336447463661085 30498693355626167798872907)
      ·
        refine ⟨45748040033439251698309361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30498693355626167798872907 45748040033439251698309361)
        ·
          refine ⟨34311030025079438773732021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45748040033439251698309361 34311030025079438773732021)
          ·
            refine ⟨3216659064851197385037377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34311030025079438773732021 3216659064851197385037377)
            ·
              refine ⟨2412494298638398038778033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3216659064851197385037377 2412494298638398038778033)
              ·
                refine ⟨1809370723978798529083525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2412494298638398038778033 1809370723978798529083525)
                ·
                  refine ⟨339257010746024724203161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1809370723978798529083525 339257010746024724203161)
                  ·
                    rfl

theorem cell22_2973153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 4].length) (baseStart_2973153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973153 prefixEnd_2973153 := by exact prefixLift 2973153
  have htrace : WordTrace (prefixWord ++ tailWord_2973153) baseStart_2973153 baseEnd_2973153 := by
    simpa [prefixWord, tailWord_2973153, baseEnd_2973153] using wordTrace_append hprefix tailTrace_2973153
  have hstable : (prefixWord ++ tailWord_2973153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973153).length < 2 ^ (prefixWord ++ tailWord_2973153).sum := by decide
  have hdescent : baseEnd_2973153 < baseStart_2973153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973177 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 4, 6]
def baseStart_2973177 : Nat := 118140960795 + 2973177 * 2 ^ 59
def prefixEnd_2973177 : Nat := 4983230072969 + 3 ^ 40 * 2973177 * 2
def baseEnd_2973177 : Nat := 1017779247928546110009409

theorem tailTrace_2973177 : CollatzResearch.WordTrace tailWord_2973177 prefixEnd_2973177 1017779247928546110009409 := by
  unfold tailWord_2973177
  simp only [CollatzResearch.WordTrace]
  refine ⟨108440673949694982050421785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72293782633129988033614523 108440673949694982050421785)
  ·
    refine ⟨81330505462271236537816339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108440673949694982050421785 81330505462271236537816339)
    ·
      refine ⟨121995758193406854806724509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81330505462271236537816339 121995758193406854806724509)
      ·
        refine ⟨45748409322527570552521691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121995758193406854806724509 45748409322527570552521691)
        ·
          refine ⟨68622613983791355828782537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45748409322527570552521691 68622613983791355828782537)
          ·
            refine ⟨51466960487843516871586903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68622613983791355828782537 51466960487843516871586903)
            ·
              refine ⟨77200440731765275307380355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51466960487843516871586903 77200440731765275307380355)
              ·
                refine ⟨115800661097647912961070533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77200440731765275307380355 115800661097647912961070533)
                ·
                  refine ⟨21712623955808983680200725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115800661097647912961070533 21712623955808983680200725)
                  ·
                    refine ⟨1017779247928546110009409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21712623955808983680200725 1017779247928546110009409)
                    ·
                      rfl

theorem cell22_2973177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_2973177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973177 prefixEnd_2973177 := by exact prefixLift 2973177
  have htrace : WordTrace (prefixWord ++ tailWord_2973177) baseStart_2973177 baseEnd_2973177 := by
    simpa [prefixWord, tailWord_2973177, baseEnd_2973177] using wordTrace_append hprefix tailTrace_2973177
  have hstable : (prefixWord ++ tailWord_2973177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973177).length < 2 ^ (prefixWord ++ tailWord_2973177).sum := by decide
  have hdescent : baseEnd_2973177 < baseStart_2973177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973179 : List Nat := [1, 1, 1, 1, 1, 3, 2, 6, 3, 3]
def baseStart_2973179 : Nat := 118140960795 + 2973179 * 2 ^ 59
def prefixEnd_2973179 : Nat := 4983230072969 + 3 ^ 40 * 2973179 * 2
def baseEnd_2973179 : Nat := 1017779932569418771459403

theorem tailTrace_2973179 : CollatzResearch.WordTrace tailWord_2973179 prefixEnd_2973179 1017779932569418771459403 := by
  unfold tailWord_2973179
  simp only [CollatzResearch.WordTrace]
  refine ⟨108440746895687736391994591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72293831263791824261329727 108440746895687736391994591)
  ·
    refine ⟨162661120343531604587991887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108440746895687736391994591 162661120343531604587991887)
    ·
      refine ⟨243991680515297406881987831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162661120343531604587991887 243991680515297406881987831)
      ·
        refine ⟨365987520772946110322981747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243991680515297406881987831 365987520772946110322981747)
        ·
          refine ⟨548981281159419165484472621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365987520772946110322981747 548981281159419165484472621)
          ·
            refine ⟨205867980434782187056677233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 548981281159419165484472621 205867980434782187056677233)
            ·
              refine ⟨154400985326086640292507925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205867980434782187056677233 154400985326086640292507925)
              ·
                refine ⟨7237546187160311263711309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154400985326086640292507925 7237546187160311263711309)
                ·
                  refine ⟨2714079820185116723891741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7237546187160311263711309 2714079820185116723891741)
                  ·
                    refine ⟨1017779932569418771459403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2714079820185116723891741 1017779932569418771459403)
                    ·
                      rfl

theorem cell22_2973179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 3].length) (baseStart_2973179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973179 prefixEnd_2973179 := by exact prefixLift 2973179
  have htrace : WordTrace (prefixWord ++ tailWord_2973179) baseStart_2973179 baseEnd_2973179 := by
    simpa [prefixWord, tailWord_2973179, baseEnd_2973179] using wordTrace_append hprefix tailTrace_2973179
  have hstable : (prefixWord ++ tailWord_2973179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973179).length < 2 ^ (prefixWord ++ tailWord_2973179).sum := by decide
  have hdescent : baseEnd_2973179 < baseStart_2973179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973213 : List Nat := [1, 4, 2, 2, 1, 1, 1, 6, 1, 3]
def baseStart_2973213 : Nat := 118140960795 + 2973213 * 2 ^ 59
def prefixEnd_2973213 : Nat := 4983230072969 + 3 ^ 40 * 2973213 * 2
def baseEnd_2973213 : Nat := 1017791571464254016109299

theorem tailTrace_2973213 : CollatzResearch.WordTrace tailWord_2973213 prefixEnd_2973213 1017791571464254016109299 := by
  unfold tailWord_2973213
  simp only [CollatzResearch.WordTrace]
  refine ⟨108441986977564560198732293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72294657985043040132488195 108441986977564560198732293)
  ·
    refine ⟨20332872558293355037262305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108441986977564560198732293 20332872558293355037262305)
    ·
      refine ⟨15249654418720016277946729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20332872558293355037262305 15249654418720016277946729)
      ·
        refine ⟨11437240814040012208460047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15249654418720016277946729 11437240814040012208460047)
        ·
          refine ⟨17155861221060018312690071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11437240814040012208460047 17155861221060018312690071)
          ·
            refine ⟨25733791831590027469035107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17155861221060018312690071 25733791831590027469035107)
            ·
              refine ⟨38600687747385041203552661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25733791831590027469035107 38600687747385041203552661)
              ·
                refine ⟨1809407238158673806416531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38600687747385041203552661 1809407238158673806416531)
                ·
                  refine ⟨2714110857238010709624797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1809407238158673806416531 2714110857238010709624797)
                  ·
                    refine ⟨1017791571464254016109299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2714110857238010709624797 1017791571464254016109299)
                    ·
                      rfl

theorem cell22_2973213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_2973213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973213 prefixEnd_2973213 := by exact prefixLift 2973213
  have htrace : WordTrace (prefixWord ++ tailWord_2973213) baseStart_2973213 baseEnd_2973213 := by
    simpa [prefixWord, tailWord_2973213, baseEnd_2973213] using wordTrace_append hprefix tailTrace_2973213
  have hstable : (prefixWord ++ tailWord_2973213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973213).length < 2 ^ (prefixWord ++ tailWord_2973213).sum := by decide
  have hdescent : baseEnd_2973213 < baseStart_2973213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973271 : List Nat := [1, 1, 3, 2, 2, 5, 1, 1, 6]
def baseStart_2973271 : Nat := 118140960795 + 2973271 * 2 ^ 59
def prefixEnd_2973271 : Nat := 4983230072969 + 3 ^ 40 * 2973271 * 2
def baseEnd_2973271 : Nat := 339270475349853732719707

theorem tailTrace_2973271 : CollatzResearch.WordTrace tailWord_2973271 prefixEnd_2973271 339270475349853732719707 := by
  unfold tailWord_2973271
  simp only [CollatzResearch.WordTrace]
  refine ⟨108444102411354436104343667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72296068274236290736229111 108444102411354436104343667)
  ·
    refine ⟨162666153617031654156515501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108444102411354436104343667 162666153617031654156515501)
    ·
      refine ⟨60999807606386870308693313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162666153617031654156515501 60999807606386870308693313)
      ·
        refine ⟨45749855704790152731519985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60999807606386870308693313 45749855704790152731519985)
        ·
          refine ⟨34312391778592614548639989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45749855704790152731519985 34312391778592614548639989)
          ·
            refine ⟨3216786729243057613934999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34312391778592614548639989 3216786729243057613934999)
            ·
              refine ⟨4825180093864586420902499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3216786729243057613934999 4825180093864586420902499)
              ·
                refine ⟨7237770140796879631353749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4825180093864586420902499 7237770140796879631353749)
                ·
                  refine ⟨339270475349853732719707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7237770140796879631353749 339270475349853732719707)
                  ·
                    rfl

theorem cell22_2973271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 6].length) (baseStart_2973271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973271 prefixEnd_2973271 := by exact prefixLift 2973271
  have htrace : WordTrace (prefixWord ++ tailWord_2973271) baseStart_2973271 baseEnd_2973271 := by
    simpa [prefixWord, tailWord_2973271, baseEnd_2973271] using wordTrace_append hprefix tailTrace_2973271
  have hstable : (prefixWord ++ tailWord_2973271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973271).length < 2 ^ (prefixWord ++ tailWord_2973271).sum := by decide
  have hdescent : baseEnd_2973271 < baseStart_2973271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973277 : List Nat := [1, 4, 4, 2, 1, 2, 2, 1, 5]
def baseStart_2973277 : Nat := 118140960795 + 2973277 * 2 ^ 59
def prefixEnd_2973277 : Nat := 4983230072969 + 3 ^ 40 * 2973277 * 2
def baseEnd_2973277 : Nat := 339271159990726394169701

theorem tailTrace_2973277 : CollatzResearch.WordTrace tailWord_2973277 prefixEnd_2973277 339271159990726394169701 := by
  unfold tailWord_2973277
  simp only [CollatzResearch.WordTrace]
  refine ⟨108444321249332699129062085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72296214166221799419374723 108444321249332699129062085)
  ·
    refine ⟨20333310234249881086699141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108444321249332699129062085 20333310234249881086699141)
    ·
      refine ⟨3812495668921852703756089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20333310234249881086699141 3812495668921852703756089)
      ·
        refine ⟨2859371751691389527817067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3812495668921852703756089 2859371751691389527817067)
        ·
          refine ⟨4289057627537084291725601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2859371751691389527817067 4289057627537084291725601)
          ·
            refine ⟨3216793220652813218794201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4289057627537084291725601 3216793220652813218794201)
            ·
              refine ⟨2412594915489609914095651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3216793220652813218794201 2412594915489609914095651)
              ·
                refine ⟨3618892373234414871143477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2412594915489609914095651 3618892373234414871143477)
                ·
                  refine ⟨339271159990726394169701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3618892373234414871143477 339271159990726394169701)
                  ·
                    rfl

theorem cell22_2973277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_2973277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973277 prefixEnd_2973277 := by exact prefixLift 2973277
  have htrace : WordTrace (prefixWord ++ tailWord_2973277) baseStart_2973277 baseEnd_2973277 := by
    simpa [prefixWord, tailWord_2973277, baseEnd_2973277] using wordTrace_append hprefix tailTrace_2973277
  have hstable : (prefixWord ++ tailWord_2973277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973277).length < 2 ^ (prefixWord ++ tailWord_2973277).sum := by decide
  have hdescent : baseEnd_2973277 < baseStart_2973277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973316 : List Nat := [2, 3, 2, 1, 5, 9]
def baseStart_2973316 : Nat := 118140960795 + 2973316 * 2 ^ 59
def prefixEnd_2973316 : Nat := 4983230072969 + 3 ^ 40 * 2973316 * 2
def baseEnd_2973316 : Nat := 12565763339125877540543

theorem tailTrace_2973316 : CollatzResearch.WordTrace tailWord_2973316 prefixEnd_2973316 12565763339125877540543 := by
  unfold tailWord_2973316
  simp only [CollatzResearch.WordTrace]
  refine ⟨54222871848095704394865901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72297162464127605859821201 54222871848095704394865901)
  ·
    refine ⟨20333576943035889148074713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54222871848095704394865901 20333576943035889148074713)
    ·
      refine ⟨15250182707276916861056035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20333576943035889148074713 15250182707276916861056035)
      ·
        refine ⟨22875274060915375291584053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15250182707276916861056035 22875274060915375291584053)
        ·
          refine ⟨2144556943210816433586005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22875274060915375291584053 2144556943210816433586005)
          ·
            refine ⟨12565763339125877540543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2144556943210816433586005 12565763339125877540543)
            ·
              rfl

theorem cell22_2973316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 9].length) (baseStart_2973316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973316 prefixEnd_2973316 := by exact prefixLift 2973316
  have htrace : WordTrace (prefixWord ++ tailWord_2973316) baseStart_2973316 baseEnd_2973316 := by
    simpa [prefixWord, tailWord_2973316, baseEnd_2973316] using wordTrace_append hprefix tailTrace_2973316
  have hstable : (prefixWord ++ tailWord_2973316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973316).length < 2 ^ (prefixWord ++ tailWord_2973316).sum := by decide
  have hdescent : baseEnd_2973316 < baseStart_2973316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973348 : List Nat := [2, 3, 1, 2, 2, 3, 1, 2, 3, 3]
def baseStart_2973348 : Nat := 118140960795 + 2973348 * 2 ^ 59
def prefixEnd_2973348 : Nat := 4983230072969 + 3 ^ 40 * 2973348 * 2
def baseEnd_2973348 : Nat := 1017837784723158663983885

theorem tailTrace_2973348 : CollatzResearch.WordTrace tailWord_2973348 prefixEnd_2973348 1017837784723158663983885 := by
  unfold tailWord_2973348
  simp only [CollatzResearch.WordTrace]
  refine ⟨54223455416037739127448349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72297940554716985503264465 54223455416037739127448349)
  ·
    refine ⟨20333795781014152172793131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54223455416037739127448349 20333795781014152172793131)
    ·
      refine ⟨30500693671521228259189697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20333795781014152172793131 30500693671521228259189697)
      ·
        refine ⟨22875520253640921194392273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30500693671521228259189697 22875520253640921194392273)
        ·
          refine ⟨17156640190230690895794205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22875520253640921194392273 17156640190230690895794205)
          ·
            refine ⟨6433740071336509085922827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17156640190230690895794205 6433740071336509085922827)
            ·
              refine ⟨9650610107004763628884241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6433740071336509085922827 9650610107004763628884241)
              ·
                refine ⟨7237957580253572721663181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9650610107004763628884241 7237957580253572721663181)
                ·
                  refine ⟨2714234092595089770623693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7237957580253572721663181 2714234092595089770623693)
                  ·
                    refine ⟨1017837784723158663983885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2714234092595089770623693 1017837784723158663983885)
                    ·
                      rfl

theorem cell22_2973348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_2973348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973348 prefixEnd_2973348 := by exact prefixLift 2973348
  have htrace : WordTrace (prefixWord ++ tailWord_2973348) baseStart_2973348 baseEnd_2973348 := by
    simpa [prefixWord, tailWord_2973348, baseEnd_2973348] using wordTrace_append hprefix tailTrace_2973348
  have hstable : (prefixWord ++ tailWord_2973348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973348).length < 2 ^ (prefixWord ++ tailWord_2973348).sum := by decide
  have hdescent : baseEnd_2973348 < baseStart_2973348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973359 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 1, 7]
def baseStart_2973359 : Nat := 118140960795 + 2973359 * 2 ^ 59
def prefixEnd_2973359 : Nat := 4983230072969 + 3 ^ 40 * 2973359 * 2
def baseEnd_2973359 : Nat := 1017841550247958301958851

theorem tailTrace_2973359 : CollatzResearch.WordTrace tailWord_2973359 prefixEnd_2973359 1017841550247958301958851 := by
  unfold tailWord_2973359
  simp only [CollatzResearch.WordTrace]
  refine ⟨108447312035035627133547131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72298208023357084755698087 108447312035035627133547131)
  ·
    refine ⟨162670968052553440700320697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108447312035035627133547131 162670968052553440700320697)
    ·
      refine ⟨122003226039415080525240523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162670968052553440700320697 122003226039415080525240523)
      ·
        refine ⟨183004839059122620787860785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122003226039415080525240523 183004839059122620787860785)
        ·
          refine ⟨137253629294341965590895589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183004839059122620787860785 137253629294341965590895589)
          ·
            refine ⟨25735055492689118548292923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137253629294341965590895589 25735055492689118548292923)
            ·
              refine ⟨38602583239033677822439385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25735055492689118548292923 38602583239033677822439385)
              ·
                refine ⟨28951937429275258366829539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38602583239033677822439385 28951937429275258366829539)
                ·
                  refine ⟨43427906143912887550244309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28951937429275258366829539 43427906143912887550244309)
                  ·
                    refine ⟨1017841550247958301958851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43427906143912887550244309 1017841550247958301958851)
                    ·
                      rfl

theorem cell22_2973359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_2973359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973359 prefixEnd_2973359 := by exact prefixLift 2973359
  have htrace : WordTrace (prefixWord ++ tailWord_2973359) baseStart_2973359 baseEnd_2973359 := by
    simpa [prefixWord, tailWord_2973359, baseEnd_2973359] using wordTrace_append hprefix tailTrace_2973359
  have hstable : (prefixWord ++ tailWord_2973359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973359).length < 2 ^ (prefixWord ++ tailWord_2973359).sum := by decide
  have hdescent : baseEnd_2973359 < baseStart_2973359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973382 : List Nat := [6, 1, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_2973382 : Nat := 118140960795 + 2973382 * 2 ^ 59
def prefixEnd_2973382 : Nat := 4983230072969 + 3 ^ 40 * 2973382 * 2
def baseEnd_2973382 : Nat := 1017849423617993908633781

theorem tailTrace_2973382 : CollatzResearch.WordTrace tailWord_2973382 prefixEnd_2973382 1017849423617993908633781 := by
  unfold tailWord_2973382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3389004716061009439426075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72298767275968201374422933 3389004716061009439426075)
  ·
    refine ⟨5083507074091514159139113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3389004716061009439426075 5083507074091514159139113)
    ·
      refine ⟨3812630305568635619354335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5083507074091514159139113 3812630305568635619354335)
      ·
        refine ⟨5718945458352953429031503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3812630305568635619354335 5718945458352953429031503)
        ·
          refine ⟨8578418187529430143547255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5718945458352953429031503 8578418187529430143547255)
          ·
            refine ⟨12867627281294145215320883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8578418187529430143547255 12867627281294145215320883)
            ·
              refine ⟨19301440921941217822981325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12867627281294145215320883 19301440921941217822981325)
              ·
                refine ⟨7238040345727956683617997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19301440921941217822981325 7238040345727956683617997)
                ·
                  refine ⟨2714265129647983756356749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7238040345727956683617997 2714265129647983756356749)
                  ·
                    refine ⟨1017849423617993908633781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2714265129647983756356749 1017849423617993908633781)
                    ·
                      rfl

theorem cell22_2973382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_2973382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973382 prefixEnd_2973382 := by exact prefixLift 2973382
  have htrace : WordTrace (prefixWord ++ tailWord_2973382) baseStart_2973382 baseEnd_2973382 := by
    simpa [prefixWord, tailWord_2973382, baseEnd_2973382] using wordTrace_append hprefix tailTrace_2973382
  have hstable : (prefixWord ++ tailWord_2973382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973382).length < 2 ^ (prefixWord ++ tailWord_2973382).sum := by decide
  have hdescent : baseEnd_2973382 < baseStart_2973382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973446 : List Nat := [6, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_2973446 : Nat := 118140960795 + 2973446 * 2 ^ 59
def prefixEnd_2973446 : Nat := 4983230072969 + 3 ^ 40 * 2973446 * 2
def baseEnd_2973446 : Nat := 339290444041973025011195

theorem tailTrace_2973446 : CollatzResearch.WordTrace tailWord_2973446 prefixEnd_2973446 339290444041973025011195 := by
  unfold tailWord_2973446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3389077662053763780998881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72300323457146960661309461 3389077662053763780998881)
  ·
    refine ⟨2541808246540322835749161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3389077662053763780998881 2541808246540322835749161)
    ·
      refine ⟨1906356184905242126811871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2541808246540322835749161 1906356184905242126811871)
      ·
        refine ⟨2859534277357863190217807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1906356184905242126811871 2859534277357863190217807)
        ·
          refine ⟨4289301416036794785326711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2859534277357863190217807 4289301416036794785326711)
          ·
            refine ⟨6433952124055192177990067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4289301416036794785326711 6433952124055192177990067)
            ·
              refine ⟨9650928186082788266985101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6433952124055192177990067 9650928186082788266985101)
              ·
                refine ⟨3619098069781045600119413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9650928186082788266985101 3619098069781045600119413)
                ·
                  refine ⟨339290444041973025011195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3619098069781045600119413 339290444041973025011195)
                  ·
                    rfl

theorem cell22_2973446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_2973446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973446 prefixEnd_2973446 := by exact prefixLift 2973446
  have htrace : WordTrace (prefixWord ++ tailWord_2973446) baseStart_2973446 baseEnd_2973446 := by
    simpa [prefixWord, tailWord_2973446, baseEnd_2973446] using wordTrace_append hprefix tailTrace_2973446
  have hstable : (prefixWord ++ tailWord_2973446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973446).length < 2 ^ (prefixWord ++ tailWord_2973446).sum := by decide
  have hdescent : baseEnd_2973446 < baseStart_2973446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973511 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 1, 7]
def baseStart_2973511 : Nat := 118140960795 + 2973511 * 2 ^ 59
def prefixEnd_2973511 : Nat := 4983230072969 + 3 ^ 40 * 2973511 * 2
def baseEnd_2973511 : Nat := 1017893582954280572158385

theorem tailTrace_2973511 : CollatzResearch.WordTrace tailWord_2973511 prefixEnd_2973511 1017893582954280572158385 := by
  unfold tailWord_2973511
  simp only [CollatzResearch.WordTrace]
  refine ⟨108452855930484957093080387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72301903953656638062053591 108452855930484957093080387)
  ·
    refine ⟨162679283895727435639620581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108452855930484957093080387 162679283895727435639620581)
    ·
      refine ⟨30502365730448894182428859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162679283895727435639620581 30502365730448894182428859)
      ·
        refine ⟨45753548595673341273643289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30502365730448894182428859 45753548595673341273643289)
        ·
          refine ⟨34315161446755005955232467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45753548595673341273643289 34315161446755005955232467)
          ·
            refine ⟨51472742170132508932848701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34315161446755005955232467 51472742170132508932848701)
            ·
              refine ⟨19302278313799690849818263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51472742170132508932848701 19302278313799690849818263)
              ·
                refine ⟨28953417470699536274727395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19302278313799690849818263 28953417470699536274727395)
                ·
                  refine ⟨43430126206049304412091093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28953417470699536274727395 43430126206049304412091093)
                  ·
                    refine ⟨1017893582954280572158385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43430126206049304412091093 1017893582954280572158385)
                    ·
                      rfl

theorem cell22_2973511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_2973511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973511 prefixEnd_2973511 := by exact prefixLift 2973511
  have htrace : WordTrace (prefixWord ++ tailWord_2973511) baseStart_2973511 baseEnd_2973511 := by
    simpa [prefixWord, tailWord_2973511, baseEnd_2973511] using wordTrace_append hprefix tailTrace_2973511
  have hstable : (prefixWord ++ tailWord_2973511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973511).length < 2 ^ (prefixWord ++ tailWord_2973511).sum := by decide
  have hdescent : baseEnd_2973511 < baseStart_2973511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973517 : List Nat := [1, 6, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_2973517 : Nat := 118140960795 + 2973517 * 2 ^ 59
def prefixEnd_2973517 : Nat := 4983230072969 + 3 ^ 40 * 2973517 * 2
def baseEnd_2973517 : Nat := 1017895636876898556508367

theorem tailTrace_2973517 : CollatzResearch.WordTrace tailWord_2973517 prefixEnd_2973517 1017895636876898556508367 := by
  unfold tailWord_2973517
  simp only [CollatzResearch.WordTrace]
  refine ⟨108453074768463220117798805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72302049845642146745199203 108453074768463220117798805)
  ·
    refine ⟨5083737879771713443021819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 108453074768463220117798805 5083737879771713443021819)
    ·
      refine ⟨7625606819657570164532729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5083737879771713443021819 7625606819657570164532729)
      ·
        refine ⟨5719205114743177623399547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7625606819657570164532729 5719205114743177623399547)
        ·
          refine ⟨8578807672114766435099321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5719205114743177623399547 8578807672114766435099321)
          ·
            refine ⟨6434105754086074826324491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8578807672114766435099321 6434105754086074826324491)
            ·
              refine ⟨9651158631129112239486737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6434105754086074826324491 9651158631129112239486737)
              ·
                refine ⟨7238368973346834179615053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9651158631129112239486737 7238368973346834179615053)
                ·
                  refine ⟨2714388365005062817355645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7238368973346834179615053 2714388365005062817355645)
                  ·
                    refine ⟨1017895636876898556508367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2714388365005062817355645 1017895636876898556508367)
                    ·
                      rfl

theorem cell22_2973517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_2973517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973517 prefixEnd_2973517 := by exact prefixLift 2973517
  have htrace : WordTrace (prefixWord ++ tailWord_2973517) baseStart_2973517 baseEnd_2973517 := by
    simpa [prefixWord, tailWord_2973517, baseEnd_2973517] using wordTrace_append hprefix tailTrace_2973517
  have hstable : (prefixWord ++ tailWord_2973517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973517).length < 2 ^ (prefixWord ++ tailWord_2973517).sum := by decide
  have hdescent : baseEnd_2973517 < baseStart_2973517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973541 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 10]
def baseStart_2973541 : Nat := 118140960795 + 2973541 * 2 ^ 59
def prefixEnd_2973541 : Nat := 4983230072969 + 3 ^ 40 * 2973541 * 2
def baseEnd_2973541 : Nat := 339301284189123497969431

theorem tailTrace_2973541 : CollatzResearch.WordTrace tailWord_2973541 prefixEnd_2973541 339301284189123497969431 := by
  unfold tailWord_2973541
  simp only [CollatzResearch.WordTrace]
  refine ⟨108453950120376272216672477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72302633413584181477781651 108453950120376272216672477)
  ·
    refine ⟨40670231295141102081252179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108453950120376272216672477 40670231295141102081252179)
    ·
      refine ⟨61005346942711653121878269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40670231295141102081252179 61005346942711653121878269)
      ·
        refine ⟨22877005103516869920704351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61005346942711653121878269 22877005103516869920704351)
        ·
          refine ⟨34315507655275304881056527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22877005103516869920704351 34315507655275304881056527)
          ·
            refine ⟨51473261482912957321584791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34315507655275304881056527 51473261482912957321584791)
            ·
              refine ⟨77209892224369435982377187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51473261482912957321584791 77209892224369435982377187)
              ·
                refine ⟨115814838336554153973565781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77209892224369435982377187 115814838336554153973565781)
                ·
                  refine ⟨339301284189123497969431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 115814838336554153973565781 339301284189123497969431)
                  ·
                    rfl

theorem cell22_2973541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_2973541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973541 prefixEnd_2973541 := by exact prefixLift 2973541
  have htrace : WordTrace (prefixWord ++ tailWord_2973541) baseStart_2973541 baseEnd_2973541 := by
    simpa [prefixWord, tailWord_2973541, baseEnd_2973541] using wordTrace_append hprefix tailTrace_2973541
  have hstable : (prefixWord ++ tailWord_2973541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973541).length < 2 ^ (prefixWord ++ tailWord_2973541).sum := by decide
  have hdescent : baseEnd_2973541 < baseStart_2973541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973660 : List Nat := [2, 2, 6, 1, 2, 1, 2, 2, 4]
def baseStart_2973660 : Nat := 118140960795 + 2973660 * 2 ^ 59
def prefixEnd_2973660 : Nat := 4983230072969 + 3 ^ 40 * 2973660 * 2
def baseEnd_2973660 : Nat := 339314862899764616727643

theorem tailTrace_2973660 : CollatzResearch.WordTrace tailWord_2973660 prefixEnd_2973660 339314862899764616727643 := by
  unfold tailWord_2973660
  simp only [CollatzResearch.WordTrace]
  refine ⟨54229145203472577770127217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72305526937963437026836289 54229145203472577770127217)
  ·
    refine ⟨40671858902604433327595413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54229145203472577770127217 40671858902604433327595413)
    ·
      refine ⟨1906493386059582812231035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40671858902604433327595413 1906493386059582812231035)
      ·
        refine ⟨2859740079089374218346553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1906493386059582812231035 2859740079089374218346553)
        ·
          refine ⟨2144805059317030663759915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2859740079089374218346553 2144805059317030663759915)
          ·
            refine ⟨3217207588975545995639873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2144805059317030663759915 3217207588975545995639873)
            ·
              refine ⟨2412905691731659496729905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3217207588975545995639873 2412905691731659496729905)
              ·
                refine ⟨1809679268798744622547429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2412905691731659496729905 1809679268798744622547429)
                ·
                  refine ⟨339314862899764616727643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1809679268798744622547429 339314862899764616727643)
                  ·
                    rfl

theorem cell22_2973660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_2973660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973660 prefixEnd_2973660 := by exact prefixLift 2973660
  have htrace : WordTrace (prefixWord ++ tailWord_2973660) baseStart_2973660 baseEnd_2973660 := by
    simpa [prefixWord, tailWord_2973660, baseEnd_2973660] using wordTrace_append hprefix tailTrace_2973660
  have hstable : (prefixWord ++ tailWord_2973660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973660).length < 2 ^ (prefixWord ++ tailWord_2973660).sum := by decide
  have hdescent : baseEnd_2973660 < baseStart_2973660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973693 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 8]
def baseStart_2973693 : Nat := 118140960795 + 2973693 * 2 ^ 59
def prefixEnd_2973693 : Nat := 4983230072969 + 3 ^ 40 * 2973693 * 2
def baseEnd_2973693 : Nat := 339318628424564254702609

theorem tailTrace_2973693 : CollatzResearch.WordTrace tailWord_2973693 prefixEnd_2973693 339318628424564254702609 := by
  unfold tailWord_2973693
  simp only [CollatzResearch.WordTrace]
  refine ⟨108459494015825602176205733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72306329343883734784137155 108459494015825602176205733)
  ·
    refine ⟨20336155127967300408038575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108459494015825602176205733 20336155127967300408038575)
    ·
      refine ⟨30504232691950950612057863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20336155127967300408038575 30504232691950950612057863)
      ·
        refine ⟨45756349037926425918086795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30504232691950950612057863 45756349037926425918086795)
        ·
          refine ⟨68634523556889638877130193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45756349037926425918086795 68634523556889638877130193)
          ·
            refine ⟨51475892667667229157847645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68634523556889638877130193 51475892667667229157847645)
            ·
              refine ⟨19303459750375210934192867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51475892667667229157847645 19303459750375210934192867)
              ·
                refine ⟨28955189625562816401289301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19303459750375210934192867 28955189625562816401289301)
                ·
                  refine ⟨339318628424564254702609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28955189625562816401289301 339318628424564254702609)
                  ·
                    rfl

theorem cell22_2973693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_2973693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973693 prefixEnd_2973693 := by exact prefixLift 2973693
  have htrace : WordTrace (prefixWord ++ tailWord_2973693) baseStart_2973693 baseEnd_2973693 := by
    simpa [prefixWord, tailWord_2973693, baseEnd_2973693] using wordTrace_append hprefix tailTrace_2973693
  have hstable : (prefixWord ++ tailWord_2973693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973693).length < 2 ^ (prefixWord ++ tailWord_2973693).sum := by decide
  have hdescent : baseEnd_2973693 < baseStart_2973693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973716 : List Nat := [2, 4, 3, 2, 1, 2, 1, 2, 5]
def baseStart_2973716 : Nat := 118140960795 + 2973716 * 2 ^ 59
def prefixEnd_2973716 : Nat := 4983230072969 + 3 ^ 40 * 2973716 * 2
def baseEnd_2973716 : Nat := 339321252881242790260919

theorem tailTrace_2973716 : CollatzResearch.WordTrace tailWord_2973716 prefixEnd_2973716 339321252881242790260919 := by
  unfold tailWord_2973716
  simp only [CollatzResearch.WordTrace]
  refine ⟨54230166447371138552146501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72306888596494851402862001 54230166447371138552146501)
  ·
    refine ⟨10168156208882088478527469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54230166447371138552146501 10168156208882088478527469)
    ·
      refine ⟨3813058578330783179447801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10168156208882088478527469 3813058578330783179447801)
      ·
        refine ⟨2859793933748087384585851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3813058578330783179447801 2859793933748087384585851)
        ·
          refine ⟨4289690900622131076878777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2859793933748087384585851 4289690900622131076878777)
          ·
            refine ⟨3217268175466598307659083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4289690900622131076878777 3217268175466598307659083)
            ·
              refine ⟨4825902263199897461488625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217268175466598307659083 4825902263199897461488625)
              ·
                refine ⟨3619426697399923096116469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4825902263199897461488625 3619426697399923096116469)
                ·
                  refine ⟨339321252881242790260919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3619426697399923096116469 339321252881242790260919)
                  ·
                    rfl

theorem cell22_2973716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_2973716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973716 prefixEnd_2973716 := by exact prefixLift 2973716
  have htrace : WordTrace (prefixWord ++ tailWord_2973716) baseStart_2973716 baseEnd_2973716 := by
    simpa [prefixWord, tailWord_2973716, baseEnd_2973716] using wordTrace_append hprefix tailTrace_2973716
  have hstable : (prefixWord ++ tailWord_2973716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973716).length < 2 ^ (prefixWord ++ tailWord_2973716).sum := by decide
  have hdescent : baseEnd_2973716 < baseStart_2973716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973742 : List Nat := [4, 1, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_2973742 : Nat := 118140960795 + 2973742 * 2 ^ 59
def prefixEnd_2973742 : Nat := 4983230072969 + 3 ^ 40 * 2973742 * 2
def baseEnd_2973742 : Nat := 1017972658975072969632677

theorem tailTrace_2973742 : CollatzResearch.WordTrace tailWord_2973742 prefixEnd_2973742 1017972658975072969632677 := by
  unfold tailWord_2973742
  simp only [CollatzResearch.WordTrace]
  refine ⟨13557660149081010443092435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72307520795098722363159653 13557660149081010443092435)
  ·
    refine ⟨20336490223621515664638653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13557660149081010443092435 20336490223621515664638653)
    ·
      refine ⟨7626183833858068374239495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20336490223621515664638653 7626183833858068374239495)
      ·
        refine ⟨11439275750787102561359243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7626183833858068374239495 11439275750787102561359243)
        ·
          refine ⟨17158913626180653842038865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11439275750787102561359243 17158913626180653842038865)
          ·
            refine ⟨12869185219635490381529149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17158913626180653842038865 12869185219635490381529149)
            ·
              refine ⟨4825944457363308893073431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12869185219635490381529149 4825944457363308893073431)
              ·
                refine ⟨7238916686044963339610147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4825944457363308893073431 7238916686044963339610147)
                ·
                  refine ⟨10858375029067445009415221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7238916686044963339610147 10858375029067445009415221)
                  ·
                    refine ⟨1017972658975072969632677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10858375029067445009415221 1017972658975072969632677)
                    ·
                      rfl

theorem cell22_2973742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_2973742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973742 prefixEnd_2973742 := by exact prefixLift 2973742
  have htrace : WordTrace (prefixWord ++ tailWord_2973742) baseStart_2973742 baseEnd_2973742 := by
    simpa [prefixWord, tailWord_2973742, baseEnd_2973742] using wordTrace_append hprefix tailTrace_2973742
  have hstable : (prefixWord ++ tailWord_2973742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973742).length < 2 ^ (prefixWord ++ tailWord_2973742).sum := by decide
  have hdescent : baseEnd_2973742 < baseStart_2973742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973845 : List Nat := [1, 3, 2, 1, 1, 1, 4, 3, 6]
def baseStart_2973845 : Nat := 118140960795 + 2973845 * 2 ^ 59
def prefixEnd_2973845 : Nat := 4983230072969 + 3 ^ 40 * 2973845 * 2
def baseEnd_2973845 : Nat := 339335972660005011435787

theorem tailTrace_2973845 : CollatzResearch.WordTrace tailWord_2973845 prefixEnd_2973845 339335972660005011435787 := by
  unfold tailWord_2973845
  simp only [CollatzResearch.WordTrace]
  refine ⟨108465037911274932135738989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72310025274183288090492659 108465037911274932135738989)
  ·
    refine ⟨40674389216728099550902121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108465037911274932135738989 40674389216728099550902121)
    ·
      refine ⟨30505791912546074663176591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40674389216728099550902121 30505791912546074663176591)
      ·
        refine ⟨45758687868819111994764887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30505791912546074663176591 45758687868819111994764887)
        ·
          refine ⟨68638031803228667992147331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45758687868819111994764887 68638031803228667992147331)
          ·
            refine ⟨102957047704843001988220997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68638031803228667992147331 102957047704843001988220997)
            ·
              refine ⟨19304446444658062872791437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102957047704843001988220997 19304446444658062872791437)
              ·
                refine ⟨7239167416746773577296789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19304446444658062872791437 7239167416746773577296789)
                ·
                  refine ⟨339335972660005011435787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7239167416746773577296789 339335972660005011435787)
                  ·
                    rfl

theorem cell22_2973845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_2973845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973845 prefixEnd_2973845 := by exact prefixLift 2973845
  have htrace : WordTrace (prefixWord ++ tailWord_2973845) baseStart_2973845 baseEnd_2973845 := by
    simpa [prefixWord, tailWord_2973845, baseEnd_2973845] using wordTrace_append hprefix tailTrace_2973845
  have hstable : (prefixWord ++ tailWord_2973845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973845).length < 2 ^ (prefixWord ++ tailWord_2973845).sum := by decide
  have hdescent : baseEnd_2973845 < baseStart_2973845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973879 : List Nat := [1, 1, 3, 1, 4, 3, 2, 3, 4]
def baseStart_2973879 : Nat := 118140960795 + 2973879 * 2 ^ 59
def prefixEnd_2973879 : Nat := 4983230072969 + 3 ^ 40 * 2973879 * 2
def baseEnd_2973879 : Nat := 339339852291616759652419

theorem tailTrace_2973879 : CollatzResearch.WordTrace tailWord_2973879 prefixEnd_2973879 339339852291616759652419 := by
  unfold tailWord_2973879
  simp only [CollatzResearch.WordTrace]
  refine ⟨108466277993151755942476691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72310851995434503961651127 108466277993151755942476691)
  ·
    refine ⟨162699416989727633913715037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108466277993151755942476691 162699416989727633913715037)
    ·
      refine ⟨61012281371147862717643139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162699416989727633913715037 61012281371147862717643139)
      ·
        refine ⟨91518422056721794076464709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61012281371147862717643139 91518422056721794076464709)
        ·
          refine ⟨17159704135635336389337133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91518422056721794076464709 17159704135635336389337133)
          ·
            refine ⟨6434889050863251146001425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17159704135635336389337133 6434889050863251146001425)
            ·
              refine ⟨4826166788147438359501069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6434889050863251146001425 4826166788147438359501069)
              ·
                refine ⟨1809812545555289384812901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4826166788147438359501069 1809812545555289384812901)
                ·
                  refine ⟨339339852291616759652419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1809812545555289384812901 339339852291616759652419)
                  ·
                    rfl

theorem cell22_2973879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 4].length) (baseStart_2973879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973879 prefixEnd_2973879 := by exact prefixLift 2973879
  have htrace : WordTrace (prefixWord ++ tailWord_2973879) baseStart_2973879 baseEnd_2973879 := by
    simpa [prefixWord, tailWord_2973879, baseEnd_2973879] using wordTrace_append hprefix tailTrace_2973879
  have hstable : (prefixWord ++ tailWord_2973879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973879).length < 2 ^ (prefixWord ++ tailWord_2973879).sum := by decide
  have hdescent : baseEnd_2973879 < baseStart_2973879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973969 : List Nat := [1, 2, 2, 1, 1, 5, 4, 1, 5]
def baseStart_2973969 : Nat := 118140960795 + 2973969 * 2 ^ 59
def prefixEnd_2973969 : Nat := 4983230072969 + 3 ^ 40 * 2973969 * 2
def baseEnd_2973969 : Nat := 339350121904706681402327

theorem tailTrace_2973969 : CollatzResearch.WordTrace tailWord_2973969 prefixEnd_2973969 339350121904706681402327 := by
  unfold tailWord_2973969
  simp only [CollatzResearch.WordTrace]
  refine ⟨108469560562825701313252961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72313040375217134208835307 108469560562825701313252961)
  ·
    refine ⟨81352170422119275984939721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108469560562825701313252961 81352170422119275984939721)
    ·
      refine ⟨61014127816589456988704791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81352170422119275984939721 61014127816589456988704791)
      ·
        refine ⟨91521191724884185483057187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61014127816589456988704791 91521191724884185483057187)
        ·
          refine ⟨137281787587326278224585781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91521191724884185483057187 137281787587326278224585781)
          ·
            refine ⟨12870167586311838583554917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137281787587326278224585781 12870167586311838583554917)
            ·
              refine ⟨2413156422433469734416547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12870167586311838583554917 2413156422433469734416547)
              ·
                refine ⟨3619734633650204601624821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2413156422433469734416547 3619734633650204601624821)
                ·
                  refine ⟨339350121904706681402327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3619734633650204601624821 339350121904706681402327)
                  ·
                    rfl

theorem cell22_2973969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 5].length) (baseStart_2973969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2973969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2973969 prefixEnd_2973969 := by exact prefixLift 2973969
  have htrace : WordTrace (prefixWord ++ tailWord_2973969) baseStart_2973969 baseEnd_2973969 := by
    simpa [prefixWord, tailWord_2973969, baseEnd_2973969] using wordTrace_append hprefix tailTrace_2973969
  have hstable : (prefixWord ++ tailWord_2973969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973969).length < 2 ^ (prefixWord ++ tailWord_2973969).sum := by decide
  have hdescent : baseEnd_2973969 < baseStart_2973969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974012 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 3, 5]
def baseStart_2974012 : Nat := 118140960795 + 2974012 * 2 ^ 59
def prefixEnd_2974012 : Nat := 4983230072969 + 3 ^ 40 * 2974012 * 2
def baseEnd_2974012 : Nat := 1018065085492882265381849

theorem tailTrace_2974012 : CollatzResearch.WordTrace tailWord_2974012 prefixEnd_2974012 1018065085492882265381849 := by
  unfold tailWord_2974012
  simp only [CollatzResearch.WordTrace]
  refine ⟨54235564450834959828534145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72314085934446613104712193 54235564450834959828534145)
  ·
    refine ⟨40676673338126219871400609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54235564450834959828534145 40676673338126219871400609)
    ·
      refine ⟨30507505003594664903550457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40676673338126219871400609 30507505003594664903550457)
      ·
        refine ⟨22880628752695998677662843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30507505003594664903550457 22880628752695998677662843)
        ·
          refine ⟨34320943129043998016494265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22880628752695998677662843 34320943129043998016494265)
          ·
            refine ⟨25740707346782998512370699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34320943129043998016494265 25740707346782998512370699)
            ·
              refine ⟨38611061020174497768556049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25740707346782998512370699 38611061020174497768556049)
              ·
                refine ⟨28958295765130873326417037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38611061020174497768556049 28958295765130873326417037)
                ·
                  refine ⟨10859360911924077497406389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28958295765130873326417037 10859360911924077497406389)
                  ·
                    refine ⟨1018065085492882265381849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10859360911924077497406389 1018065085492882265381849)
                    ·
                      rfl

theorem cell22_2974012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_2974012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974012 prefixEnd_2974012 := by exact prefixLift 2974012
  have htrace : WordTrace (prefixWord ++ tailWord_2974012) baseStart_2974012 baseEnd_2974012 := by
    simpa [prefixWord, tailWord_2974012, baseEnd_2974012] using wordTrace_append hprefix tailTrace_2974012
  have hstable : (prefixWord ++ tailWord_2974012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974012).length < 2 ^ (prefixWord ++ tailWord_2974012).sum := by decide
  have hdescent : baseEnd_2974012 < baseStart_2974012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974104 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 7]
def baseStart_2974104 : Nat := 118140960795 + 2974104 * 2 ^ 59
def prefixEnd_2974104 : Nat := 4983230072969 + 3 ^ 40 * 2974104 * 2
def baseEnd_2974104 : Nat := 339365526324341564027189

theorem tailTrace_2974104 : CollatzResearch.WordTrace tailWord_2974104 prefixEnd_2974104 339365526324341564027189 := by
  unfold tailWord_2974104
  simp only [CollatzResearch.WordTrace]
  refine ⟨54237242208668309684708683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72316322944891079579611577 54237242208668309684708683)
  ·
    refine ⟨81355863313002464527063025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54237242208668309684708683 81355863313002464527063025)
    ·
      refine ⟨61016897484751848395297269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81355863313002464527063025 61016897484751848395297269)
      ·
        refine ⟨5720334139195485787059119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61016897484751848395297269 5720334139195485787059119)
        ·
          refine ⟨8580501208793228680588679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5720334139195485787059119 8580501208793228680588679)
          ·
            refine ⟨12870751813189843020883019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8580501208793228680588679 12870751813189843020883019)
            ·
              refine ⟨19306127719784764531324529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12870751813189843020883019 19306127719784764531324529)
              ·
                refine ⟨14479595789838573398493397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19306127719784764531324529 14479595789838573398493397)
                ·
                  refine ⟨339365526324341564027189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14479595789838573398493397 339365526324341564027189)
                  ·
                    rfl

theorem cell22_2974104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 7].length) (baseStart_2974104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974104 prefixEnd_2974104 := by exact prefixLift 2974104
  have htrace : WordTrace (prefixWord ++ tailWord_2974104) baseStart_2974104 baseEnd_2974104 := by
    simpa [prefixWord, tailWord_2974104, baseEnd_2974104] using wordTrace_append hprefix tailTrace_2974104
  have hstable : (prefixWord ++ tailWord_2974104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974104).length < 2 ^ (prefixWord ++ tailWord_2974104).sum := by decide
  have hdescent : baseEnd_2974104 < baseStart_2974104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974125 : List Nat := [1, 5, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_2974125 : Nat := 118140960795 + 2974125 * 2 ^ 59
def prefixEnd_2974125 : Nat := 4983230072969 + 3 ^ 40 * 2974125 * 2
def baseEnd_2974125 : Nat := 1018103767702187637306503

theorem tailTrace_2974125 : CollatzResearch.WordTrace tailWord_2974125 prefixEnd_2974125 1018103767702187637306503 := by
  unfold tailWord_2974125
  simp only [CollatzResearch.WordTrace]
  refine ⟨108475250350260539955931829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72316833566840359970621219 108475250350260539955931829)
  ·
    refine ⟨10169554720336925620868609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108475250350260539955931829 10169554720336925620868609)
    ·
      refine ⟨7627166040252694215651457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10169554720336925620868609 7627166040252694215651457)
      ·
        refine ⟨5720374530189520661738593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7627166040252694215651457 5720374530189520661738593)
        ·
          refine ⟨4290280897642140496303945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5720374530189520661738593 4290280897642140496303945)
          ·
            refine ⟨3217710673231605372227959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4290280897642140496303945 3217710673231605372227959)
            ·
              refine ⟨4826566009847408058341939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217710673231605372227959 4826566009847408058341939)
              ·
                refine ⟨7239849014771112087512909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4826566009847408058341939 7239849014771112087512909)
                ·
                  refine ⟨2714943380539167032817341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7239849014771112087512909 2714943380539167032817341)
                  ·
                    refine ⟨1018103767702187637306503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2714943380539167032817341 1018103767702187637306503)
                    ·
                      rfl

theorem cell22_2974125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_2974125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974125 prefixEnd_2974125 := by exact prefixLift 2974125
  have htrace : WordTrace (prefixWord ++ tailWord_2974125) baseStart_2974125 baseEnd_2974125 := by
    simpa [prefixWord, tailWord_2974125, baseEnd_2974125] using wordTrace_append hprefix tailTrace_2974125
  have hstable : (prefixWord ++ tailWord_2974125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974125).length < 2 ^ (prefixWord ++ tailWord_2974125).sum := by decide
  have hdescent : baseEnd_2974125 < baseStart_2974125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974151 : List Nat := [1, 1, 4, 1, 1, 4, 3, 2, 1, 4]
def baseStart_2974151 : Nat := 118140960795 + 2974151 * 2 ^ 59
def prefixEnd_2974151 : Nat := 4983230072969 + 3 ^ 40 * 2974151 * 2
def baseEnd_2974151 : Nat := 1018112668033532236156423

theorem tailTrace_2974151 : CollatzResearch.WordTrace tailWord_2974151 prefixEnd_2974151 1018112668033532236156423 := by
  unfold tailWord_2974151
  simp only [CollatzResearch.WordTrace]
  refine ⟨108476198648166346396378307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72317465765444230930918871 108476198648166346396378307)
  ·
    refine ⟨162714297972249519594567461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108476198648166346396378307 162714297972249519594567461)
    ·
      refine ⟨30508930869796784923981399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162714297972249519594567461 30508930869796784923981399)
      ·
        refine ⟨45763396304695177385972099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30508930869796784923981399 45763396304695177385972099)
        ·
          refine ⟨68645094457042766078958149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45763396304695177385972099 68645094457042766078958149)
          ·
            refine ⟨12870955210695518639804653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68645094457042766078958149 12870955210695518639804653)
            ·
              refine ⟨4826608204010819489926745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12870955210695518639804653 4826608204010819489926745)
              ·
                refine ⟨3619956153008114617445059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4826608204010819489926745 3619956153008114617445059)
                ·
                  refine ⟨5429934229512171926167589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3619956153008114617445059 5429934229512171926167589)
                  ·
                    refine ⟨1018112668033532236156423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5429934229512171926167589 1018112668033532236156423)
                    ·
                      rfl

theorem cell22_2974151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_2974151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974151 prefixEnd_2974151 := by exact prefixLift 2974151
  have htrace : WordTrace (prefixWord ++ tailWord_2974151) baseStart_2974151 baseEnd_2974151 := by
    simpa [prefixWord, tailWord_2974151, baseEnd_2974151] using wordTrace_append hprefix tailTrace_2974151
  have hstable : (prefixWord ++ tailWord_2974151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974151).length < 2 ^ (prefixWord ++ tailWord_2974151).sum := by decide
  have hdescent : baseEnd_2974151 < baseStart_2974151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974198 : List Nat := [5, 1, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_2974198 : Nat := 118140960795 + 2974198 * 2 ^ 59
def prefixEnd_2974198 : Nat := 4983230072969 + 3 ^ 40 * 2974198 * 2
def baseEnd_2974198 : Nat := 1018128757094039780231279

theorem tailTrace_2974198 : CollatzResearch.WordTrace tailWord_2974198 prefixEnd_2974198 1018128757094039780231279 := by
  unfold tailWord_2974198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6779869554937254588958703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72318608585997382282226165 6779869554937254588958703)
  ·
    refine ⟨10169804332405881883438055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6779869554937254588958703 10169804332405881883438055)
    ·
      refine ⟨15254706498608822825157083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10169804332405881883438055 15254706498608822825157083)
      ·
        refine ⟨22882059747913234237735625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15254706498608822825157083 22882059747913234237735625)
        ·
          refine ⟨17161544810934925678301719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22882059747913234237735625 17161544810934925678301719)
          ·
            refine ⟨25742317216402388517452579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17161544810934925678301719 25742317216402388517452579)
            ·
              refine ⟨38613475824603582776178869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25742317216402388517452579 38613475824603582776178869)
              ·
                refine ⟨3620013358556585885266769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38613475824603582776178869 3620013358556585885266769)
                ·
                  refine ⟨2715010018917439413950077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3620013358556585885266769 2715010018917439413950077)
                  ·
                    refine ⟨1018128757094039780231279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2715010018917439413950077 1018128757094039780231279)
                    ·
                      rfl

theorem cell22_2974198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_2974198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974198 prefixEnd_2974198 := by exact prefixLift 2974198
  have htrace : WordTrace (prefixWord ++ tailWord_2974198) baseStart_2974198 baseEnd_2974198 := by
    simpa [prefixWord, tailWord_2974198, baseEnd_2974198] using wordTrace_append hprefix tailTrace_2974198
  have hstable : (prefixWord ++ tailWord_2974198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974198).length < 2 ^ (prefixWord ++ tailWord_2974198).sum := by decide
  have hdescent : baseEnd_2974198 < baseStart_2974198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974243 : List Nat := [1, 1, 1, 4, 4, 2, 2, 1, 3, 3]
def baseStart_2974243 : Nat := 118140960795 + 2974243 * 2 ^ 59
def prefixEnd_2974243 : Nat := 4983230072969 + 3 ^ 40 * 2974243 * 2
def baseEnd_2974243 : Nat := 1018144161513674662856141

theorem tailTrace_2974243 : CollatzResearch.WordTrace tailWord_2974243 prefixEnd_2974243 1018144161513674662856141 := by
  unfold tailWord_2974243
  simp only [CollatzResearch.WordTrace]
  refine ⟨108479554163833046108727383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72319702775888697405818255 108479554163833046108727383)
  ·
    refine ⟨162719331245749569163091075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108479554163833046108727383 162719331245749569163091075)
    ·
      refine ⟨244078996868624353744636613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162719331245749569163091075 244078996868624353744636613)
      ·
        refine ⟨45764811912867066327119365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244078996868624353744636613 45764811912867066327119365)
        ·
          refine ⟨8580902233662574936334881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45764811912867066327119365 8580902233662574936334881)
          ·
            refine ⟨6435676675246931202251161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8580902233662574936334881 6435676675246931202251161)
            ·
              refine ⟨4826757506435198401688371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6435676675246931202251161 4826757506435198401688371)
              ·
                refine ⟨7240136259652797602532557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4826757506435198401688371 7240136259652797602532557)
                ·
                  refine ⟨2715051097369799100949709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7240136259652797602532557 2715051097369799100949709)
                  ·
                    refine ⟨1018144161513674662856141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2715051097369799100949709 1018144161513674662856141)
                    ·
                      rfl

theorem cell22_2974243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 3].length) (baseStart_2974243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974243 prefixEnd_2974243 := by exact prefixLift 2974243
  have htrace : WordTrace (prefixWord ++ tailWord_2974243) baseStart_2974243 baseEnd_2974243 := by
    simpa [prefixWord, tailWord_2974243, baseEnd_2974243] using wordTrace_append hprefix tailTrace_2974243
  have hstable : (prefixWord ++ tailWord_2974243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974243).length < 2 ^ (prefixWord ++ tailWord_2974243).sum := by decide
  have hdescent : baseEnd_2974243 < baseStart_2974243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974320 : List Nat := [2, 1, 1, 1, 7, 2, 1, 2, 1, 4]
def baseStart_2974320 : Nat := 118140960795 + 2974320 * 2 ^ 59
def prefixEnd_2974320 : Nat := 4983230072969 + 3 ^ 40 * 2974320 * 2
def baseEnd_2974320 : Nat := 1018170520187272128680905

theorem tailTrace_2974320 : CollatzResearch.WordTrace tailWord_2974320 prefixEnd_2974320 1018170520187272128680905 := by
  unfold tailWord_2974320
  simp only [CollatzResearch.WordTrace]
  refine ⟨54241181292277044129640207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72321575056369392172853609 54241181292277044129640207)
  ·
    refine ⟨81361771938415566194460311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54241181292277044129640207 81361771938415566194460311)
    ·
      refine ⟨122042657907623349291690467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81361771938415566194460311 122042657907623349291690467)
      ·
        refine ⟨183063986861435023937535701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122042657907623349291690467 183063986861435023937535701)
        ·
          refine ⟨4290562192064883373535993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 183063986861435023937535701 4290562192064883373535993)
          ·
            refine ⟨3217921644048662530151995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4290562192064883373535993 3217921644048662530151995)
            ·
              refine ⟨4826882466072993795227993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217921644048662530151995 4826882466072993795227993)
              ·
                refine ⟨3620161849554745346420995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4826882466072993795227993 3620161849554745346420995)
                ·
                  refine ⟨5430242774332118019631493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3620161849554745346420995 5430242774332118019631493)
                  ·
                    refine ⟨1018170520187272128680905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5430242774332118019631493 1018170520187272128680905)
                    ·
                      rfl

theorem cell22_2974320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 1, 4].length) (baseStart_2974320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974320 prefixEnd_2974320 := by exact prefixLift 2974320
  have htrace : WordTrace (prefixWord ++ tailWord_2974320) baseStart_2974320 baseEnd_2974320 := by
    simpa [prefixWord, tailWord_2974320, baseEnd_2974320] using wordTrace_append hprefix tailTrace_2974320
  have hstable : (prefixWord ++ tailWord_2974320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974320).length < 2 ^ (prefixWord ++ tailWord_2974320).sum := by decide
  have hdescent : baseEnd_2974320 < baseStart_2974320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974333 : List Nat := [1, 4, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_2974333 : Nat := 118140960795 + 2974333 * 2 ^ 59
def prefixEnd_2974333 : Nat := 4983230072969 + 3 ^ 40 * 2974333 * 2
def baseEnd_2974333 : Nat := 1018174970352944428105865

theorem tailTrace_2974333 : CollatzResearch.WordTrace tailWord_2974333 prefixEnd_2974333 1018174970352944428105865 := by
  unfold tailWord_2974333
  simp only [CollatzResearch.WordTrace]
  refine ⟨108482836733506991479503653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72321891155671327653002435 108482836733506991479503653)
  ·
    refine ⟨20340531887532560902406935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108482836733506991479503653 20340531887532560902406935)
    ·
      refine ⟨30510797831298841353610403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20340531887532560902406935 30510797831298841353610403)
      ·
        refine ⟨45766196746948262030415605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30510797831298841353610403 45766196746948262030415605)
        ·
          refine ⟨4290580945026399565351463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45766196746948262030415605 4290580945026399565351463)
          ·
            refine ⟨6435871417539599348027195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4290580945026399565351463 6435871417539599348027195)
            ·
              refine ⟨9653807126309399022040793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6435871417539599348027195 9653807126309399022040793)
              ·
                refine ⟨7240355344732049266530595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9653807126309399022040793 7240355344732049266530595)
                ·
                  refine ⟨10860533017098073899795893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7240355344732049266530595 10860533017098073899795893)
                  ·
                    refine ⟨1018174970352944428105865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10860533017098073899795893 1018174970352944428105865)
                    ·
                      rfl

theorem cell22_2974333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_2974333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974333 prefixEnd_2974333 := by exact prefixLift 2974333
  have htrace : WordTrace (prefixWord ++ tailWord_2974333) baseStart_2974333 baseEnd_2974333 := by
    simpa [prefixWord, tailWord_2974333, baseEnd_2974333] using wordTrace_append hprefix tailTrace_2974333
  have hstable : (prefixWord ++ tailWord_2974333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974333).length < 2 ^ (prefixWord ++ tailWord_2974333).sum := by decide
  have hdescent : baseEnd_2974333 < baseStart_2974333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974346 : List Nat := [3, 1, 2, 3, 3, 10]
def baseStart_2974346 : Nat := 118140960795 + 2974346 * 2 ^ 59
def prefixEnd_2974346 : Nat := 4983230072969 + 3 ^ 40 * 2974346 * 2
def baseEnd_2974346 : Nat := 12570116302698971944825

theorem tailTrace_2974346 : CollatzResearch.WordTrace tailWord_2974346 prefixEnd_2974346 12570116302698971944825 := by
  unfold tailWord_2974346
  simp only [CollatzResearch.WordTrace]
  refine ⟨27120827720614973674931723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72322207254973263133151261 27120827720614973674931723)
  ·
    refine ⟨40681241580922460512397585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27120827720614973674931723 40681241580922460512397585)
    ·
      refine ⟨30510931185691845384298189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40681241580922460512397585 30510931185691845384298189)
      ·
        refine ⟨11441599194634442019111821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30510931185691845384298189 11441599194634442019111821)
        ·
          refine ⟨4290599697987915757166933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11441599194634442019111821 4290599697987915757166933)
          ·
            refine ⟨12570116302698971944825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4290599697987915757166933 12570116302698971944825)
            ·
              rfl

theorem cell22_2974346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 10].length) (baseStart_2974346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974346 prefixEnd_2974346 := by exact prefixLift 2974346
  have htrace : WordTrace (prefixWord ++ tailWord_2974346) baseStart_2974346 baseEnd_2974346 := by
    simpa [prefixWord, tailWord_2974346, baseEnd_2974346] using wordTrace_append hprefix tailTrace_2974346
  have hstable : (prefixWord ++ tailWord_2974346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974346).length < 2 ^ (prefixWord ++ tailWord_2974346).sum := by decide
  have hdescent : baseEnd_2974346 < baseStart_2974346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974350 : List Nat := [4, 1, 1, 3, 1, 1, 4, 2, 2, 3]
def baseStart_2974350 : Nat := 118140960795 + 2974350 * 2 ^ 59
def prefixEnd_2974350 : Nat := 4983230072969 + 3 ^ 40 * 2974350 * 2
def baseEnd_2974350 : Nat := 1018180789800362050430813

theorem tailTrace_2974350 : CollatzResearch.WordTrace tailWord_2974350 prefixEnd_2974350 1018180789800362050430813 := by
  unfold tailWord_2974350
  simp only [CollatzResearch.WordTrace]
  refine ⟨13560432096805675422859063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72322304516296935588581669 13560432096805675422859063)
  ·
    refine ⟨20340648145208513134288595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13560432096805675422859063 20340648145208513134288595)
    ·
      refine ⟨30510972217812769701432893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20340648145208513134288595 30510972217812769701432893)
      ·
        refine ⟨11441614581679788638037335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30510972217812769701432893 11441614581679788638037335)
        ·
          refine ⟨17162421872519682957056003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11441614581679788638037335 17162421872519682957056003)
          ·
            refine ⟨25743632808779524435584005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17162421872519682957056003 25743632808779524435584005)
            ·
              refine ⟨4826931151646160831672001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25743632808779524435584005 4826931151646160831672001)
              ·
                refine ⟨3620198363734620623754001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4826931151646160831672001 3620198363734620623754001)
                ·
                  refine ⟨2715148772800965467815501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3620198363734620623754001 2715148772800965467815501)
                  ·
                    refine ⟨1018180789800362050430813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2715148772800965467815501 1018180789800362050430813)
                    ·
                      rfl

theorem cell22_2974350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_2974350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974350 prefixEnd_2974350 := by exact prefixLift 2974350
  have htrace : WordTrace (prefixWord ++ tailWord_2974350) baseStart_2974350 baseEnd_2974350 := by
    simpa [prefixWord, tailWord_2974350, baseEnd_2974350] using wordTrace_append hprefix tailTrace_2974350
  have hstable : (prefixWord ++ tailWord_2974350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974350).length < 2 ^ (prefixWord ++ tailWord_2974350).sum := by decide
  have hdescent : baseEnd_2974350 < baseStart_2974350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974382 : List Nat := [4, 1, 4, 1, 1, 3, 1, 1, 2, 4]
def baseStart_2974382 : Nat := 118140960795 + 2974382 * 2 ^ 59
def prefixEnd_2974382 : Nat := 4983230072969 + 3 ^ 40 * 2974382 * 2
def baseEnd_2974382 : Nat := 1018191744054324633630715

theorem tailTrace_2974382 : CollatzResearch.WordTrace tailWord_2974382 prefixEnd_2974382 1018191744054324633630715 := by
  unfold tailWord_2974382
  simp only [CollatzResearch.WordTrace]
  refine ⟨13560577988791184106004675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72323082606886315232024933 13560577988791184106004675)
  ·
    refine ⟨20340866983186776159007013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13560577988791184106004675 20340866983186776159007013)
    ·
      refine ⟨3813912559347520529813815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20340866983186776159007013 3813912559347520529813815)
      ·
        refine ⟨5720868839021280794720723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3813912559347520529813815 5720868839021280794720723)
        ·
          refine ⟨8581303258531921192081085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5720868839021280794720723 8581303258531921192081085)
          ·
            refine ⟨3217988721949470447030407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8581303258531921192081085 3217988721949470447030407)
            ·
              refine ⟨4826983082924205670545611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217988721949470447030407 4826983082924205670545611)
              ·
                refine ⟨7240474624386308505818417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4826983082924205670545611 7240474624386308505818417)
                ·
                  refine ⟨5430355968289731379363813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7240474624386308505818417 5430355968289731379363813)
                  ·
                    refine ⟨1018191744054324633630715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5430355968289731379363813 1018191744054324633630715)
                    ·
                      rfl

theorem cell22_2974382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_2974382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974382 prefixEnd_2974382 := by exact prefixLift 2974382
  have htrace : WordTrace (prefixWord ++ tailWord_2974382) baseStart_2974382 baseEnd_2974382 := by
    simpa [prefixWord, tailWord_2974382, baseEnd_2974382] using wordTrace_append hprefix tailTrace_2974382
  have hstable : (prefixWord ++ tailWord_2974382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974382).length < 2 ^ (prefixWord ++ tailWord_2974382).sum := by decide
  have hdescent : baseEnd_2974382 < baseStart_2974382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974401 : List Nat := [1, 2, 6, 2, 2, 1, 1, 2, 2, 3]
def baseStart_2974401 : Nat := 118140960795 + 2974401 * 2 ^ 59
def prefixEnd_2974401 : Nat := 4983230072969 + 3 ^ 40 * 2974401 * 2
def baseEnd_2974401 : Nat := 1018198248142614917405657

theorem tailTrace_2974401 : CollatzResearch.WordTrace tailWord_2974401 prefixEnd_2974401 1018198248142614917405657 := by
  unfold tailWord_2974401
  simp only [CollatzResearch.WordTrace]
  refine ⟨108485316897260639092979057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72323544598173759395319371 108485316897260639092979057)
  ·
    refine ⟨81363987672945479319734293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108485316897260639092979057 81363987672945479319734293)
    ·
      refine ⟨3813936922169319343112545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81363987672945479319734293 3813936922169319343112545)
      ·
        refine ⟨2860452691626989507334409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3813936922169319343112545 2860452691626989507334409)
        ·
          refine ⟨2145339518720242130500807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2860452691626989507334409 2145339518720242130500807)
          ·
            refine ⟨3218009278080363195751211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2145339518720242130500807 3218009278080363195751211)
            ·
              refine ⟨4827013917120544793626817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3218009278080363195751211 4827013917120544793626817)
              ·
                refine ⟨3620260437840408595220113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4827013917120544793626817 3620260437840408595220113)
                ·
                  refine ⟨2715195328380306446415085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3620260437840408595220113 2715195328380306446415085)
                  ·
                    refine ⟨1018198248142614917405657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2715195328380306446415085 1018198248142614917405657)
                    ·
                      rfl

theorem cell22_2974401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_2974401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974401 prefixEnd_2974401 := by exact prefixLift 2974401
  have htrace : WordTrace (prefixWord ++ tailWord_2974401) baseStart_2974401 baseEnd_2974401 := by
    simpa [prefixWord, tailWord_2974401, baseEnd_2974401] using wordTrace_append hprefix tailTrace_2974401
  have hstable : (prefixWord ++ tailWord_2974401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974401).length < 2 ^ (prefixWord ++ tailWord_2974401).sum := by decide
  have hdescent : baseEnd_2974401 < baseStart_2974401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974408 : List Nat := [2, 1, 3, 1, 2, 3, 3, 2, 5]
def baseStart_2974408 : Nat := 118140960795 + 2974408 * 2 ^ 59
def prefixEnd_2974408 : Nat := 4983230072969 + 3 ^ 40 * 2974408 * 2
def baseEnd_2974408 : Nat := 339400214795223077493545

theorem tailTrace_2974408 : CollatzResearch.WordTrace tailWord_2974408 prefixEnd_2974408 339400214795223077493545 := by
  unfold tailWord_2974408
  simp only [CollatzResearch.WordTrace]
  refine ⟨54242786104117639644241939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72323714805490186192322585 54242786104117639644241939)
  ·
    refine ⟨81364179156176459466362909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54242786104117639644241939 81364179156176459466362909)
    ·
      refine ⟨30511567183566172299886091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81364179156176459466362909 30511567183566172299886091)
      ·
        refine ⟨45767350775349258449829137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30511567183566172299886091 45767350775349258449829137)
        ·
          refine ⟨34325513081511943837371853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45767350775349258449829137 34325513081511943837371853)
          ·
            refine ⟨12872067405566978939014445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34325513081511943837371853 12872067405566978939014445)
            ·
              refine ⟨4827025277087617102130417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12872067405566978939014445 4827025277087617102130417)
              ·
                refine ⟨3620268957815712826597813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4827025277087617102130417 3620268957815712826597813)
                ·
                  refine ⟨339400214795223077493545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3620268957815712826597813 339400214795223077493545)
                  ·
                    rfl

theorem cell22_2974408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 5].length) (baseStart_2974408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974408 prefixEnd_2974408 := by exact prefixLift 2974408
  have htrace : WordTrace (prefixWord ++ tailWord_2974408) baseStart_2974408 baseEnd_2974408 := by
    simpa [prefixWord, tailWord_2974408, baseEnd_2974408] using wordTrace_append hprefix tailTrace_2974408
  have hstable : (prefixWord ++ tailWord_2974408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974408).length < 2 ^ (prefixWord ++ tailWord_2974408).sum := by decide
  have hdescent : baseEnd_2974408 < baseStart_2974408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974412 : List Nat := [2, 2, 1, 5, 1, 1, 2, 4, 1, 3]
def baseStart_2974412 : Nat := 118140960795 + 2974412 * 2 ^ 59
def prefixEnd_2974412 : Nat := 4983230072969 + 3 ^ 40 * 2974412 * 2
def baseEnd_2974412 : Nat := 1018202013667414555380623

theorem tailTrace_2974412 : CollatzResearch.WordTrace tailWord_2974412 prefixEnd_2974412 1018202013667414555380623 := by
  unfold tailWord_2974412
  simp only [CollatzResearch.WordTrace]
  refine ⟨54242859050110393985814745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72323812066813858647752993 54242859050110393985814745)
  ·
    refine ⟨40682144287582795489361059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54242859050110393985814745 40682144287582795489361059)
    ·
      refine ⟨61023216431374193234041589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40682144287582795489361059 61023216431374193234041589)
      ·
        refine ⟨5720926540441330615691399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61023216431374193234041589 5720926540441330615691399)
        ·
          refine ⟨8581389810661995923537099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5720926540441330615691399 8581389810661995923537099)
          ·
            refine ⟨12872084715992993885305649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8581389810661995923537099 12872084715992993885305649)
            ·
              refine ⟨9654063536994745413979237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12872084715992993885305649 9654063536994745413979237)
              ·
                refine ⟨1810136913186514765121107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9654063536994745413979237 1810136913186514765121107)
                ·
                  refine ⟨2715205369779772147681661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1810136913186514765121107 2715205369779772147681661)
                  ·
                    refine ⟨1018202013667414555380623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2715205369779772147681661 1018202013667414555380623)
                    ·
                      rfl

theorem cell22_2974412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 1, 3].length) (baseStart_2974412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974412 prefixEnd_2974412 := by exact prefixLift 2974412
  have htrace : WordTrace (prefixWord ++ tailWord_2974412) baseStart_2974412 baseEnd_2974412 := by
    simpa [prefixWord, tailWord_2974412, baseEnd_2974412] using wordTrace_append hprefix tailTrace_2974412
  have hstable : (prefixWord ++ tailWord_2974412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974412).length < 2 ^ (prefixWord ++ tailWord_2974412).sum := by decide
  have hdescent : baseEnd_2974412 < baseStart_2974412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974451 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 3, 5]
def baseStart_2974451 : Nat := 118140960795 + 2974451 * 2 ^ 59
def prefixEnd_2974451 : Nat := 4983230072969 + 3 ^ 40 * 2974451 * 2
def baseEnd_2974451 : Nat := 1018215364164431453655503

theorem tailTrace_2974451 : CollatzResearch.WordTrace tailWord_2974451 prefixEnd_2974451 1018215364164431453655503 := by
  unfold tailWord_2974451
  simp only [CollatzResearch.WordTrace]
  refine ⟨108487140547079497632299207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72324760364719665088199471 108487140547079497632299207)
  ·
    refine ⟨162730710820619246448448811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108487140547079497632299207 162730710820619246448448811)
    ·
      refine ⟨244096066230928869672673217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162730710820619246448448811 244096066230928869672673217)
      ·
        refine ⟨183072049673196652254504913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244096066230928869672673217 183072049673196652254504913)
        ·
          refine ⟨137304037254897489190878685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183072049673196652254504913 137304037254897489190878685)
          ·
            refine ⟨51489013970586558446579507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137304037254897489190878685 51489013970586558446579507)
            ·
              refine ⟨77233520955879837669869261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51489013970586558446579507 77233520955879837669869261)
              ·
                refine ⟨28962570358454939126200973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77233520955879837669869261 28962570358454939126200973)
                ·
                  refine ⟨10860963884420602172325365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28962570358454939126200973 10860963884420602172325365)
                  ·
                    refine ⟨1018215364164431453655503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10860963884420602172325365 1018215364164431453655503)
                    ·
                      rfl

theorem cell22_2974451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 5].length) (baseStart_2974451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974451 prefixEnd_2974451 := by exact prefixLift 2974451
  have htrace : WordTrace (prefixWord ++ tailWord_2974451) baseStart_2974451 baseEnd_2974451 := by
    simpa [prefixWord, tailWord_2974451, baseEnd_2974451] using wordTrace_append hprefix tailTrace_2974451
  have hstable : (prefixWord ++ tailWord_2974451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974451).length < 2 ^ (prefixWord ++ tailWord_2974451).sum := by decide
  have hdescent : baseEnd_2974451 < baseStart_2974451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974481 : List Nat := [1, 2, 2, 1, 1, 3, 3, 9]
def baseStart_2974481 : Nat := 118140960795 + 2974481 * 2 ^ 59
def prefixEnd_2974481 : Nat := 4983230072969 + 3 ^ 40 * 2974481 * 2
def baseEnd_2974481 : Nat := 113136181530835708378379

theorem tailTrace_2974481 : CollatzResearch.WordTrace tailWord_2974481 prefixEnd_2974481 113136181530835708378379 := by
  unfold tailWord_2974481
  simp only [CollatzResearch.WordTrace]
  refine ⟨108488234736970812755891297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72325489824647208503927531 108488234736970812755891297)
  ·
    refine ⟨81366176052728109566918473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108488234736970812755891297 81366176052728109566918473)
    ·
      refine ⟨61024632039546082175188855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81366176052728109566918473 61024632039546082175188855)
      ·
        refine ⟨91536948059319123262783283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61024632039546082175188855 91536948059319123262783283)
        ·
          refine ⟨137305422088978684894174925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91536948059319123262783283 137305422088978684894174925)
          ·
            refine ⟨51489533283367006835315597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137305422088978684894174925 51489533283367006835315597)
            ·
              refine ⟨19308574981262627563243349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51489533283367006835315597 19308574981262627563243349)
              ·
                refine ⟨113136181530835708378379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19308574981262627563243349 113136181530835708378379)
                ·
                  rfl

theorem cell22_2974481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 9].length) (baseStart_2974481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974481 prefixEnd_2974481 := by exact prefixLift 2974481
  have htrace : WordTrace (prefixWord ++ tailWord_2974481) baseStart_2974481 baseEnd_2974481 := by
    simpa [prefixWord, tailWord_2974481, baseEnd_2974481] using wordTrace_append hprefix tailTrace_2974481
  have hstable : (prefixWord ++ tailWord_2974481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974481).length < 2 ^ (prefixWord ++ tailWord_2974481).sum := by decide
  have hdescent : baseEnd_2974481 < baseStart_2974481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974485 : List Nat := [1, 3, 2, 1, 2, 2, 3, 3, 2, 3]
def baseStart_2974485 : Nat := 118140960795 + 2974485 * 2 ^ 59
def prefixEnd_2974485 : Nat := 4983230072969 + 3 ^ 40 * 2974485 * 2
def baseEnd_2974485 : Nat := 1018227003059266698305399

theorem tailTrace_2974485 : CollatzResearch.WordTrace tailWord_2974485 prefixEnd_2974485 1018227003059266698305399 := by
  unfold tailWord_2974485
  simp only [CollatzResearch.WordTrace]
  refine ⟨108488380628956321439036909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72325587085970880959357939 108488380628956321439036909)
  ·
    refine ⟨40683142735858620539638841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108488380628956321439036909 40683142735858620539638841)
    ·
      refine ⟨30512357051893965404729131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40683142735858620539638841 30512357051893965404729131)
      ·
        refine ⟨45768535577840948107093697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30512357051893965404729131 45768535577840948107093697)
        ·
          refine ⟨34326401683380711080320273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45768535577840948107093697 34326401683380711080320273)
          ·
            refine ⟨25744801262535533310240205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34326401683380711080320273 25744801262535533310240205)
            ·
              refine ⟨9654300473450824991340077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25744801262535533310240205 9654300473450824991340077)
              ·
                refine ⟨3620362677544059371752529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9654300473450824991340077 3620362677544059371752529)
                ·
                  refine ⟨2715272008158044528814397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3620362677544059371752529 2715272008158044528814397)
                  ·
                    refine ⟨1018227003059266698305399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2715272008158044528814397 1018227003059266698305399)
                    ·
                      rfl

theorem cell22_2974485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_2974485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974485 prefixEnd_2974485 := by exact prefixLift 2974485
  have htrace : WordTrace (prefixWord ++ tailWord_2974485) baseStart_2974485 baseEnd_2974485 := by
    simpa [prefixWord, tailWord_2974485, baseEnd_2974485] using wordTrace_append hprefix tailTrace_2974485
  have hstable : (prefixWord ++ tailWord_2974485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974485).length < 2 ^ (prefixWord ++ tailWord_2974485).sum := by decide
  have hdescent : baseEnd_2974485 < baseStart_2974485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974498 : List Nat := [3, 3, 1, 1, 2, 2, 2, 8]
def baseStart_2974498 : Nat := 118140960795 + 2974498 * 2 ^ 59
def prefixEnd_2974498 : Nat := 4983230072969 + 3 ^ 40 * 2974498 * 2
def baseEnd_2974498 : Nat := 113136828136104333081151

theorem tailTrace_2974498 : CollatzResearch.WordTrace tailWord_2974498 prefixEnd_2974498 113136828136104333081151 := by
  unfold tailWord_2974498
  simp only [CollatzResearch.WordTrace]
  refine ⟨27122213694477306164815037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72325903185272816439506765 27122213694477306164815037)
  ·
    refine ⟨10170830135428989811805639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27122213694477306164815037 10170830135428989811805639)
    ·
      refine ⟨15256245203143484717708459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10170830135428989811805639 15256245203143484717708459)
      ·
        refine ⟨22884367804715227076562689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15256245203143484717708459 22884367804715227076562689)
        ·
          refine ⟨17163275853536420307422017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22884367804715227076562689 17163275853536420307422017)
          ·
            refine ⟨12872456890152315230566513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17163275853536420307422017 12872456890152315230566513)
            ·
              refine ⟨9654342667614236422924885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12872456890152315230566513 9654342667614236422924885)
              ·
                refine ⟨113136828136104333081151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9654342667614236422924885 113136828136104333081151)
                ·
                  rfl

theorem cell22_2974498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 8].length) (baseStart_2974498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974498 prefixEnd_2974498 := by exact prefixLift 2974498
  have htrace : WordTrace (prefixWord ++ tailWord_2974498) baseStart_2974498 baseEnd_2974498 := by
    simpa [prefixWord, tailWord_2974498, baseEnd_2974498] using wordTrace_append hprefix tailTrace_2974498
  have hstable : (prefixWord ++ tailWord_2974498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974498).length < 2 ^ (prefixWord ++ tailWord_2974498).sum := by decide
  have hdescent : baseEnd_2974498 < baseStart_2974498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974511 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 3, 8]
def baseStart_2974511 : Nat := 118140960795 + 2974511 * 2 ^ 59
def prefixEnd_2974511 : Nat := 4983230072969 + 3 ^ 40 * 2974511 * 2
def baseEnd_2974511 : Nat := 1018235903390611297155319

theorem tailTrace_2974511 : CollatzResearch.WordTrace tailWord_2974511 prefixEnd_2974511 1018235903390611297155319 := by
  unfold tailWord_2974511
  simp only [CollatzResearch.WordTrace]
  refine ⟨108489328926862127879483387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72326219284574751919655591 108489328926862127879483387)
  ·
    refine ⟨162733993390293191819225081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108489328926862127879483387 162733993390293191819225081)
    ·
      refine ⟨122050495042719893864418811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162733993390293191819225081 122050495042719893864418811)
      ·
        refine ⟨183075742564079840796628217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122050495042719893864418811 183075742564079840796628217)
        ·
          refine ⟨137306806923059880597471163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183075742564079840796628217 137306806923059880597471163)
          ·
            refine ⟨205960210384589820896206745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137306806923059880597471163 205960210384589820896206745)
            ·
              refine ⟨154470157788442365672155059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205960210384589820896206745 154470157788442365672155059)
              ·
                refine ⟨231705236682663548508232589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154470157788442365672155059 231705236682663548508232589)
                ·
                  refine ⟨86889463755998830690587221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231705236682663548508232589 86889463755998830690587221)
                  ·
                    refine ⟨1018235903390611297155319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86889463755998830690587221 1018235903390611297155319)
                    ·
                      rfl

theorem cell22_2974511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_2974511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974511 prefixEnd_2974511 := by exact prefixLift 2974511
  have htrace : WordTrace (prefixWord ++ tailWord_2974511) baseStart_2974511 baseEnd_2974511 := by
    simpa [prefixWord, tailWord_2974511, baseEnd_2974511] using wordTrace_append hprefix tailTrace_2974511
  have hstable : (prefixWord ++ tailWord_2974511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974511).length < 2 ^ (prefixWord ++ tailWord_2974511).sum := by decide
  have hdescent : baseEnd_2974511 < baseStart_2974511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974564 : List Nat := [2, 3, 1, 1, 4, 2, 2, 3, 1, 3]
def baseStart_2974564 : Nat := 118140960795 + 2974564 * 2 ^ 59
def prefixEnd_2974564 : Nat := 4983230072969 + 3 ^ 40 * 2974564 * 2
def baseEnd_2974564 : Nat := 1018254046373736825580157

theorem tailTrace_2974564 : CollatzResearch.WordTrace tailWord_2974564 prefixEnd_2974564 1018254046373736825580157 := by
  unfold tailWord_2974564
  simp only [CollatzResearch.WordTrace]
  refine ⟨54245630997835058965581373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72327507997113411954108497 54245630997835058965581373)
  ·
    refine ⟨20342111624188147112093015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54245630997835058965581373 20342111624188147112093015)
    ·
      refine ⟨30513167436282220668139523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20342111624188147112093015 30513167436282220668139523)
      ·
        refine ⟨45769751154423331002209285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30513167436282220668139523 45769751154423331002209285)
        ·
          refine ⟨8581828341454374562914241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45769751154423331002209285 8581828341454374562914241)
          ·
            refine ⟨6436371256090780922185681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8581828341454374562914241 6436371256090780922185681)
            ·
              refine ⟨4827278442068085691639261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6436371256090780922185681 4827278442068085691639261)
              ·
                refine ⟨1810229415775532134364723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4827278442068085691639261 1810229415775532134364723)
                ·
                  refine ⟨2715344123663298201547085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1810229415775532134364723 2715344123663298201547085)
                  ·
                    refine ⟨1018254046373736825580157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2715344123663298201547085 1018254046373736825580157)
                    ·
                      rfl

theorem cell22_2974564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_2974564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974564 prefixEnd_2974564 := by exact prefixLift 2974564
  have htrace : WordTrace (prefixWord ++ tailWord_2974564) baseStart_2974564 baseEnd_2974564 := by
    simpa [prefixWord, tailWord_2974564, baseEnd_2974564] using wordTrace_append hprefix tailTrace_2974564
  have hstable : (prefixWord ++ tailWord_2974564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974564).length < 2 ^ (prefixWord ++ tailWord_2974564).sum := by decide
  have hdescent : baseEnd_2974564 < baseStart_2974564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974725 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 3, 4]
def baseStart_2974725 : Nat := 118140960795 + 2974725 * 2 ^ 59
def prefixEnd_2974725 : Nat := 4983230072969 + 3 ^ 40 * 2974725 * 2
def baseEnd_2974725 : Nat := 1018309159963986072304663

theorem tailTrace_2974725 : CollatzResearch.WordTrace tailWord_2974725 prefixEnd_2974725 1018309159963986072304663 := by
  unfold tailWord_2974725
  simp only [CollatzResearch.WordTrace]
  refine ⟨108497134148086842427773629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72331422765391228285182419 108497134148086842427773629)
  ·
    refine ⟨40686425305532565910415111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108497134148086842427773629 40686425305532565910415111)
    ·
      refine ⟨61029637958298848865622667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40686425305532565910415111 61029637958298848865622667)
      ·
        refine ⟨91544456937448273298434001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61029637958298848865622667 91544456937448273298434001)
        ·
          refine ⟨68658342703086204973825501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91544456937448273298434001 68658342703086204973825501)
          ·
            refine ⟨25746878513657326865184563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68658342703086204973825501 25746878513657326865184563)
            ·
              refine ⟨38620317770485990297776845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25746878513657326865184563 38620317770485990297776845)
              ·
                refine ⟨14482619163932246361666317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38620317770485990297776845 14482619163932246361666317)
                ·
                  refine ⟨5430982186474592385624869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14482619163932246361666317 5430982186474592385624869)
                  ·
                    refine ⟨1018309159963986072304663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5430982186474592385624869 1018309159963986072304663)
                    ·
                      rfl

theorem cell22_2974725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_2974725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974725 prefixEnd_2974725 := by exact prefixLift 2974725
  have htrace : WordTrace (prefixWord ++ tailWord_2974725) baseStart_2974725 baseEnd_2974725 := by
    simpa [prefixWord, tailWord_2974725, baseEnd_2974725] using wordTrace_append hprefix tailTrace_2974725
  have hstable : (prefixWord ++ tailWord_2974725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974725).length < 2 ^ (prefixWord ++ tailWord_2974725).sum := by decide
  have hdescent : baseEnd_2974725 < baseStart_2974725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974757 : List Nat := [1, 3, 1, 2, 2, 2, 1, 6, 4]
def baseStart_2974757 : Nat := 118140960795 + 2974757 * 2 ^ 59
def prefixEnd_2974757 : Nat := 4983230072969 + 3 ^ 40 * 2974757 * 2
def baseEnd_2974757 : Nat := 339440038072649551834855

theorem tailTrace_2974757 : CollatzResearch.WordTrace tailWord_2974757 prefixEnd_2974757 339440038072649551834855 := by
  unfold tailWord_2974757
  simp only [CollatzResearch.WordTrace]
  refine ⟨108498301283970911892938525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72332200855980607928625683 108498301283970911892938525)
  ·
    refine ⟨40686862981489091959851947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108498301283970911892938525 40686862981489091959851947)
    ·
      refine ⟨61030294472233637939777921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40686862981489091959851947 61030294472233637939777921)
      ·
        refine ⟨45772720854175228454833441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61030294472233637939777921 45772720854175228454833441)
        ·
          refine ⟨34329540640631421341125081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45772720854175228454833441 34329540640631421341125081)
          ·
            refine ⟨25747155480473566005843811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34329540640631421341125081 25747155480473566005843811)
            ·
              refine ⟨38620733220710349008765717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25747155480473566005843811 38620733220710349008765717)
              ·
                refine ⟨1810346869720797609785893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38620733220710349008765717 1810346869720797609785893)
                ·
                  refine ⟨339440038072649551834855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1810346869720797609785893 339440038072649551834855)
                  ·
                    rfl

theorem cell22_2974757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_2974757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974757 prefixEnd_2974757 := by exact prefixLift 2974757
  have htrace : WordTrace (prefixWord ++ tailWord_2974757) baseStart_2974757 baseEnd_2974757 := by
    simpa [prefixWord, tailWord_2974757, baseEnd_2974757] using wordTrace_append hprefix tailTrace_2974757
  have hstable : (prefixWord ++ tailWord_2974757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974757).length < 2 ^ (prefixWord ++ tailWord_2974757).sum := by decide
  have hdescent : baseEnd_2974757 < baseStart_2974757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974770 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_2974770 : Nat := 118140960795 + 2974770 * 2 ^ 59
def prefixEnd_2974770 : Nat := 4983230072969 + 3 ^ 40 * 2974770 * 2
def baseEnd_2974770 : Nat := 1018324564383620954929525

theorem tailTrace_2974770 : CollatzResearch.WordTrace tailWord_2974770 prefixEnd_2974770 1018324564383620954929525 := by
  unfold tailWord_2974770
  simp only [CollatzResearch.WordTrace]
  refine ⟨27124693858230953778290441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72332516955282543408774509 27124693858230953778290441)
  ·
    refine ⟨20343520393673215333717831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27124693858230953778290441 20343520393673215333717831)
    ·
      refine ⟨30515280590509823000576747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20343520393673215333717831 30515280590509823000576747)
      ·
        refine ⟨45772920885764734500865121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30515280590509823000576747 45772920885764734500865121)
        ·
          refine ⟨34329690664323550875648841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45772920885764734500865121 34329690664323550875648841)
          ·
            refine ⟨25747267998242663156736631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34329690664323550875648841 25747267998242663156736631)
            ·
              refine ⟨38620901997363994735104947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25747267998242663156736631 38620901997363994735104947)
              ·
                refine ⟨57931352996045992102657421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38620901997363994735104947 57931352996045992102657421)
                ·
                  refine ⟨21724257373517247038496533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57931352996045992102657421 21724257373517247038496533)
                  ·
                    refine ⟨1018324564383620954929525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21724257373517247038496533 1018324564383620954929525)
                    ·
                      rfl

theorem cell22_2974770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_2974770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974770 prefixEnd_2974770 := by exact prefixLift 2974770
  have htrace : WordTrace (prefixWord ++ tailWord_2974770) baseStart_2974770 baseEnd_2974770 := by
    simpa [prefixWord, tailWord_2974770, baseEnd_2974770] using wordTrace_append hprefix tailTrace_2974770
  have hstable : (prefixWord ++ tailWord_2974770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974770).length < 2 ^ (prefixWord ++ tailWord_2974770).sum := by decide
  have hdescent : baseEnd_2974770 < baseStart_2974770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974802 : List Nat := [3, 2, 2, 1, 3, 3, 8]
def baseStart_2974802 : Nat := 118140960795 + 2974802 * 2 ^ 59
def prefixEnd_2974802 : Nat := 4983230072969 + 3 ^ 40 * 2974802 * 2
def baseEnd_2974802 : Nat := 37716130319910501412201

theorem tailTrace_2974802 : CollatzResearch.WordTrace tailWord_2974802 prefixEnd_2974802 37716130319910501412201 := by
  unfold tailWord_2974802
  simp only [CollatzResearch.WordTrace]
  refine ⟨27124985642201971144581665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72333295045871923052217773 27124985642201971144581665)
  ·
    refine ⟨20343739231651478358436249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27124985642201971144581665 20343739231651478358436249)
    ·
      refine ⟨15257804423738608768827187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20343739231651478358436249 15257804423738608768827187)
      ·
        refine ⟨22886706635607913153240781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15257804423738608768827187 22886706635607913153240781)
        ·
          refine ⟨8582514988352967432465293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22886706635607913153240781 8582514988352967432465293)
          ·
            refine ⟨3218443120632362787174485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8582514988352967432465293 3218443120632362787174485)
            ·
              refine ⟨37716130319910501412201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3218443120632362787174485 37716130319910501412201)
              ·
                rfl

theorem cell22_2974802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 8].length) (baseStart_2974802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974802 prefixEnd_2974802 := by exact prefixLift 2974802
  have htrace : WordTrace (prefixWord ++ tailWord_2974802) baseStart_2974802 baseEnd_2974802 := by
    simpa [prefixWord, tailWord_2974802, baseEnd_2974802] using wordTrace_append hprefix tailTrace_2974802
  have hstable : (prefixWord ++ tailWord_2974802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974802).length < 2 ^ (prefixWord ++ tailWord_2974802).sum := by decide
  have hdescent : baseEnd_2974802 < baseStart_2974802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974815 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 2, 6]
def baseStart_2974815 : Nat := 118140960795 + 2974815 * 2 ^ 59
def prefixEnd_2974815 : Nat := 4983230072969 + 3 ^ 40 * 2974815 * 2
def baseEnd_2974815 : Nat := 1018339968803255837554387

theorem tailTrace_2974815 : CollatzResearch.WordTrace tailWord_2974815 prefixEnd_2974815 1018339968803255837554387 := by
  unfold tailWord_2974815
  simp only [CollatzResearch.WordTrace]
  refine ⟨108500416717760787798549899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72333611145173858532366599 108500416717760787798549899)
  ·
    refine ⟨162750625076641181697824849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108500416717760787798549899 162750625076641181697824849)
    ·
      refine ⟨122062968807480886273368637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162750625076641181697824849 122062968807480886273368637)
      ·
        refine ⟨45773613302805332352513239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122062968807480886273368637 45773613302805332352513239)
        ·
          refine ⟨68660419954207998528769859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45773613302805332352513239 68660419954207998528769859)
          ·
            refine ⟨102990629931311997793154789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68660419954207998528769859 102990629931311997793154789)
            ·
              refine ⟨19310743112120999586216523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102990629931311997793154789 19310743112120999586216523)
              ·
                refine ⟨28966114668181499379324785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19310743112120999586216523 28966114668181499379324785)
                ·
                  refine ⟨21724586001136124534493589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28966114668181499379324785 21724586001136124534493589)
                  ·
                    refine ⟨1018339968803255837554387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21724586001136124534493589 1018339968803255837554387)
                    ·
                      rfl

theorem cell22_2974815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_2974815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974815 prefixEnd_2974815 := by exact prefixLift 2974815
  have htrace : WordTrace (prefixWord ++ tailWord_2974815) baseStart_2974815 baseEnd_2974815 := by
    simpa [prefixWord, tailWord_2974815, baseEnd_2974815] using wordTrace_append hprefix tailTrace_2974815
  have hstable : (prefixWord ++ tailWord_2974815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974815).length < 2 ^ (prefixWord ++ tailWord_2974815).sum := by decide
  have hdescent : baseEnd_2974815 < baseStart_2974815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974877 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_2974877 : Nat := 118140960795 + 2974877 * 2 ^ 59
def prefixEnd_2974877 : Nat := 4983230072969 + 3 ^ 40 * 2974877 * 2
def baseEnd_2974877 : Nat := 1018361192670308342504197

theorem tailTrace_2974877 : CollatzResearch.WordTrace tailWord_2974877 prefixEnd_2974877 1018361192670308342504197 := by
  unfold tailWord_2974877
  simp only [CollatzResearch.WordTrace]
  refine ⟨108502678043536172387306885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72335118695690781591537923 108502678043536172387306885)
  ·
    refine ⟨20344252133163032322620041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108502678043536172387306885 20344252133163032322620041)
    ·
      refine ⟨15258189099872274241965031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20344252133163032322620041 15258189099872274241965031)
      ·
        refine ⟨22887283649808411362947547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15258189099872274241965031 22887283649808411362947547)
        ·
          refine ⟨34330925474712617044421321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22887283649808411362947547 34330925474712617044421321)
          ·
            refine ⟨25748194106034462783315991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34330925474712617044421321 25748194106034462783315991)
            ·
              refine ⟨38622291159051694174973987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25748194106034462783315991 38622291159051694174973987)
              ·
                refine ⟨57933436738577541262460981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38622291159051694174973987 57933436738577541262460981)
                ·
                  refine ⟨5431259694241644493355717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57933436738577541262460981 5431259694241644493355717)
                  ·
                    refine ⟨1018361192670308342504197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5431259694241644493355717 1018361192670308342504197)
                    ·
                      rfl

theorem cell22_2974877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_2974877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974877 prefixEnd_2974877 := by exact prefixLift 2974877
  have htrace : WordTrace (prefixWord ++ tailWord_2974877) baseStart_2974877 baseEnd_2974877 := by
    simpa [prefixWord, tailWord_2974877, baseEnd_2974877] using wordTrace_append hprefix tailTrace_2974877
  have hstable : (prefixWord ++ tailWord_2974877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974877).length < 2 ^ (prefixWord ++ tailWord_2974877).sum := by decide
  have hdescent : baseEnd_2974877 < baseStart_2974877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974879 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 2, 5]
def baseStart_2974879 : Nat := 118140960795 + 2974879 * 2 ^ 59
def prefixEnd_2974879 : Nat := 4983230072969 + 3 ^ 40 * 2974879 * 2
def baseEnd_2974879 : Nat := 1018361877311181003954191

theorem tailTrace_2974879 : CollatzResearch.WordTrace tailWord_2974879 prefixEnd_2974879 1018361877311181003954191 := by
  unfold tailWord_2974879
  simp only [CollatzResearch.WordTrace]
  refine ⟨108502750989528926728879691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72335167326352617819253127 108502750989528926728879691)
  ·
    refine ⟨162754126484293390093319537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108502750989528926728879691 162754126484293390093319537)
    ·
      refine ⟨122065594863220042569989653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162754126484293390093319537 122065594863220042569989653)
      ·
        refine ⟨5721824759213439495468265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122065594863220042569989653 5721824759213439495468265)
        ·
          refine ⟨4291368569410079621601199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5721824759213439495468265 4291368569410079621601199)
          ·
            refine ⟨6437052854115119432401799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4291368569410079621601199 6437052854115119432401799)
            ·
              refine ⟨9655579281172679148602699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6437052854115119432401799 9655579281172679148602699)
              ·
                refine ⟨14483368921759018722904049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9655579281172679148602699 14483368921759018722904049)
                ·
                  refine ⟨10862526691319264042178037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14483368921759018722904049 10862526691319264042178037)
                  ·
                    refine ⟨1018361877311181003954191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10862526691319264042178037 1018361877311181003954191)
                    ·
                      rfl

theorem cell22_2974879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 5].length) (baseStart_2974879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974879 prefixEnd_2974879 := by exact prefixLift 2974879
  have htrace : WordTrace (prefixWord ++ tailWord_2974879) baseStart_2974879 baseEnd_2974879 := by
    simpa [prefixWord, tailWord_2974879, baseEnd_2974879] using wordTrace_append hprefix tailTrace_2974879
  have hstable : (prefixWord ++ tailWord_2974879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974879).length < 2 ^ (prefixWord ++ tailWord_2974879).sum := by decide
  have hdescent : baseEnd_2974879 < baseStart_2974879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974902 : List Nat := [5, 1, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_2974902 : Nat := 118140960795 + 2974902 * 2 ^ 59
def prefixEnd_2974902 : Nat := 4983230072969 + 3 ^ 40 * 2974902 * 2
def baseEnd_2974902 : Nat := 1018369750681216610629121

theorem tailTrace_2974902 : CollatzResearch.WordTrace tailWord_2974902 prefixEnd_2974902 1018369750681216610629121 := by
  unfold tailWord_2974902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6781474366777850103560435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72335726578963734437977973 6781474366777850103560435)
  ·
    refine ⟨10172211550166775155340653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6781474366777850103560435 10172211550166775155340653)
    ·
      refine ⟨3814579331312540683252745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10172211550166775155340653 3814579331312540683252745)
      ·
        refine ⟨2860934498484405512439559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3814579331312540683252745 2860934498484405512439559)
        ·
          refine ⟨4291401747726608268659339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2860934498484405512439559 4291401747726608268659339)
          ·
            refine ⟨6437102621589912402989009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4291401747726608268659339 6437102621589912402989009)
            ·
              refine ⟨4827826966192434302241757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6437102621589912402989009 4827826966192434302241757)
              ·
                refine ⟨1810435112322162863340659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4827826966192434302241757 1810435112322162863340659)
                ·
                  refine ⟨2715652668483244295010989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1810435112322162863340659 2715652668483244295010989)
                  ·
                    refine ⟨1018369750681216610629121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2715652668483244295010989 1018369750681216610629121)
                    ·
                      rfl

theorem cell22_2974902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_2974902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974902 prefixEnd_2974902 := by exact prefixLift 2974902
  have htrace : WordTrace (prefixWord ++ tailWord_2974902) baseStart_2974902 baseEnd_2974902 := by
    simpa [prefixWord, tailWord_2974902, baseEnd_2974902] using wordTrace_append hprefix tailTrace_2974902
  have hstable : (prefixWord ++ tailWord_2974902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974902).length < 2 ^ (prefixWord ++ tailWord_2974902).sum := by decide
  have hdescent : baseEnd_2974902 < baseStart_2974902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974909 : List Nat := [1, 4, 1, 2, 1, 1, 3, 5, 4]
def baseStart_2974909 : Nat := 118140960795 + 2974909 * 2 ^ 59
def prefixEnd_2974909 : Nat := 4983230072969 + 3 ^ 40 * 2974909 * 2
def baseEnd_2974909 : Nat := 339457382308090308568033

theorem tailTrace_2974909 : CollatzResearch.WordTrace tailWord_2974909 prefixEnd_2974909 339457382308090308568033 := by
  unfold tailWord_2974909
  simp only [CollatzResearch.WordTrace]
  refine ⟨108503845179420241852471781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72335896786280161234981187 108503845179420241852471781)
  ·
    refine ⟨20344470971141295347338459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108503845179420241852471781 20344470971141295347338459)
    ·
      refine ⟨30516706456711943021007689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20344470971141295347338459 30516706456711943021007689)
      ·
        refine ⟨22887529842533957265755767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30516706456711943021007689 22887529842533957265755767)
        ·
          refine ⟨34331294763800935898633651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22887529842533957265755767 34331294763800935898633651)
          ·
            refine ⟨51496942145701403847950477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34331294763800935898633651 51496942145701403847950477)
            ·
              refine ⟨19311353304638026442981429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51496942145701403847950477 19311353304638026442981429)
              ·
                refine ⟨1810439372309814979029509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19311353304638026442981429 1810439372309814979029509)
                ·
                  refine ⟨339457382308090308568033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1810439372309814979029509 339457382308090308568033)
                  ·
                    rfl

theorem cell22_2974909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_2974909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974909 prefixEnd_2974909 := by exact prefixLift 2974909
  have htrace : WordTrace (prefixWord ++ tailWord_2974909) baseStart_2974909 baseEnd_2974909 := by
    simpa [prefixWord, tailWord_2974909, baseEnd_2974909] using wordTrace_append hprefix tailTrace_2974909
  have hstable : (prefixWord ++ tailWord_2974909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974909).length < 2 ^ (prefixWord ++ tailWord_2974909).sum := by decide
  have hdescent : baseEnd_2974909 < baseStart_2974909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974952 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 2, 7]
def baseStart_2974952 : Nat := 118140960795 + 2974952 * 2 ^ 59
def prefixEnd_2974952 : Nat := 4983230072969 + 3 ^ 40 * 2974952 * 2
def baseEnd_2974952 : Nat := 1018386866703033146878967

theorem tailTrace_2974952 : CollatzResearch.WordTrace tailWord_2974952 prefixEnd_2974952 1018386866703033146878967 := by
  unfold tailWord_2974952
  simp only [CollatzResearch.WordTrace]
  refine ⟨54252706759132230098143555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72336942345509640130858073 54252706759132230098143555)
  ·
    refine ⟨81379060138698345147215333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54252706759132230098143555 81379060138698345147215333)
    ·
      refine ⟨15258573776005939715102875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81379060138698345147215333 15258573776005939715102875)
      ·
        refine ⟨22887860664008909572654313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15258573776005939715102875 22887860664008909572654313)
        ·
          refine ⟨17165895498006682179490735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22887860664008909572654313 17165895498006682179490735)
          ·
            refine ⟨25748843247010023269236103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17165895498006682179490735 25748843247010023269236103)
            ·
              refine ⟨38623264870515034903854155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25748843247010023269236103 38623264870515034903854155)
              ·
                refine ⟨57934897305772552355781233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38623264870515034903854155 57934897305772552355781233)
                ·
                  refine ⟨43451172979329414266835925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57934897305772552355781233 43451172979329414266835925)
                  ·
                    refine ⟨1018386866703033146878967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43451172979329414266835925 1018386866703033146878967)
                    ·
                      rfl

theorem cell22_2974952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_2974952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974952 prefixEnd_2974952 := by exact prefixLift 2974952
  have htrace : WordTrace (prefixWord ++ tailWord_2974952) baseStart_2974952 baseEnd_2974952 := by
    simpa [prefixWord, tailWord_2974952, baseEnd_2974952] using wordTrace_append hprefix tailTrace_2974952
  have hstable : (prefixWord ++ tailWord_2974952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974952).length < 2 ^ (prefixWord ++ tailWord_2974952).sum := by decide
  have hdescent : baseEnd_2974952 < baseStart_2974952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974954 : List Nat := [3, 1, 3, 1, 1, 3, 4, 6]
def baseStart_2974954 : Nat := 118140960795 + 2974954 * 2 ^ 59
def prefixEnd_2974954 : Nat := 4983230072969 + 3 ^ 40 * 2974954 * 2
def baseEnd_2974954 : Nat := 113154172371545089814329

theorem tailTrace_2974954 : CollatzResearch.WordTrace tailWord_2974954 prefixEnd_2974954 113154172371545089814329 := by
  unfold tailWord_2974954
  simp only [CollatzResearch.WordTrace]
  refine ⟨27126371616064303634464979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72336990976171476358573277 27126371616064303634464979)
  ·
    refine ⟨40689557424096455451697469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27126371616064303634464979 40689557424096455451697469)
    ·
      refine ⟨15258584034036170794386551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40689557424096455451697469 15258584034036170794386551)
      ·
        refine ⟨22887876051054256191579827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15258584034036170794386551 22887876051054256191579827)
        ·
          refine ⟨34331814076581384287369741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22887876051054256191579827 34331814076581384287369741)
          ·
            refine ⟨12874430278718019107763653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34331814076581384287369741 12874430278718019107763653)
            ·
              refine ⟨2413955677259628582705685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12874430278718019107763653 2413955677259628582705685)
              ·
                refine ⟨113154172371545089814329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2413955677259628582705685 113154172371545089814329)
                ·
                  rfl

theorem cell22_2974954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 6].length) (baseStart_2974954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974954 prefixEnd_2974954 := by exact prefixLift 2974954
  have htrace : WordTrace (prefixWord ++ tailWord_2974954) baseStart_2974954 baseEnd_2974954 := by
    simpa [prefixWord, tailWord_2974954, baseEnd_2974954] using wordTrace_append hprefix tailTrace_2974954
  have hstable : (prefixWord ++ tailWord_2974954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974954).length < 2 ^ (prefixWord ++ tailWord_2974954).sum := by decide
  have hdescent : baseEnd_2974954 < baseStart_2974954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974997 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 1, 7]
def baseStart_2974997 : Nat := 118140960795 + 2974997 * 2 ^ 59
def prefixEnd_2974997 : Nat := 4983230072969 + 3 ^ 40 * 2974997 * 2
def baseEnd_2974997 : Nat := 1018402271122668029503829

theorem tailTrace_2974997 : CollatzResearch.WordTrace tailWord_2974997 prefixEnd_2974997 1018402271122668029503829 := by
  unfold tailWord_2974997
  simp only [CollatzResearch.WordTrace]
  refine ⟨108507054803101432881675245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72338036535400955254450163 108507054803101432881675245)
  ·
    refine ⟨40690145551163037330628217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108507054803101432881675245 40690145551163037330628217)
    ·
      refine ⟨30517609163372277997971163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40690145551163037330628217 30517609163372277997971163)
      ·
        refine ⟨45776413745058416996956745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30517609163372277997971163 45776413745058416996956745)
        ·
          refine ⟨34332310308793812747717559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45776413745058416996956745 34332310308793812747717559)
          ·
            refine ⟨51498465463190719121576339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34332310308793812747717559 51498465463190719121576339)
            ·
              refine ⟨77247698194786078682364509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51498465463190719121576339 77247698194786078682364509)
              ·
                refine ⟨28967886823044779505886691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77247698194786078682364509 28967886823044779505886691)
                ·
                  refine ⟨43451830234567169258830037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28967886823044779505886691 43451830234567169258830037)
                  ·
                    refine ⟨1018402271122668029503829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43451830234567169258830037 1018402271122668029503829)
                    ·
                      rfl

theorem cell22_2974997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_2974997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974997 prefixEnd_2974997 := by exact prefixLift 2974997
  have htrace : WordTrace (prefixWord ++ tailWord_2974997) baseStart_2974997 baseEnd_2974997 := by
    simpa [prefixWord, tailWord_2974997, baseEnd_2974997] using wordTrace_append hprefix tailTrace_2974997
  have hstable : (prefixWord ++ tailWord_2974997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974997).length < 2 ^ (prefixWord ++ tailWord_2974997).sum := by decide
  have hdescent : baseEnd_2974997 < baseStart_2974997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974999 : List Nat := [1, 1, 3, 4, 1, 1, 3, 3, 5]
def baseStart_2974999 : Nat := 118140960795 + 2974999 * 2 ^ 59
def prefixEnd_2974999 : Nat := 4983230072969 + 3 ^ 40 * 2974999 * 2
def baseEnd_2974999 : Nat := 339467651921180230317941

theorem tailTrace_2974999 : CollatzResearch.WordTrace tailWord_2974999 prefixEnd_2974999 339467651921180230317941 := by
  unfold tailWord_2974999
  simp only [CollatzResearch.WordTrace]
  refine ⟨108507127749094187223248051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72338085166062791482165367 108507127749094187223248051)
  ·
    refine ⟨162760691623641280834872077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108507127749094187223248051 162760691623641280834872077)
    ·
      refine ⟨61035259358865480313077029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162760691623641280834872077 61035259358865480313077029)
      ·
        refine ⟨11444111129787277558701943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61035259358865480313077029 11444111129787277558701943)
        ·
          refine ⟨17166166694680916338052915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11444111129787277558701943 17166166694680916338052915)
          ·
            refine ⟨25749250042021374507079373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17166166694680916338052915 25749250042021374507079373)
            ·
              refine ⟨9655968765758015440154765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25749250042021374507079373 9655968765758015440154765)
              ·
                refine ⟨3620988287159255790058037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9655968765758015440154765 3620988287159255790058037)
                ·
                  refine ⟨339467651921180230317941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3620988287159255790058037 339467651921180230317941)
                  ·
                    rfl

theorem cell22_2974999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 5].length) (baseStart_2974999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2974999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2974999 prefixEnd_2974999 := by exact prefixLift 2974999
  have htrace : WordTrace (prefixWord ++ tailWord_2974999) baseStart_2974999 baseEnd_2974999 := by
    simpa [prefixWord, tailWord_2974999, baseEnd_2974999] using wordTrace_append hprefix tailTrace_2974999
  have hstable : (prefixWord ++ tailWord_2974999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974999).length < 2 ^ (prefixWord ++ tailWord_2974999).sum := by decide
  have hdescent : baseEnd_2974999 < baseStart_2974999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975059 : List Nat := [1, 1, 1, 2, 1, 1, 8, 1, 1, 5]
def baseStart_2975059 : Nat := 118140960795 + 2975059 * 2 ^ 59
def prefixEnd_2975059 : Nat := 4983230072969 + 3 ^ 40 * 2975059 * 2
def baseEnd_2975059 : Nat := 1018423494989720534453639

theorem tailTrace_2975059 : CollatzResearch.WordTrace tailWord_2975059 prefixEnd_2975059 1018423494989720534453639 := by
  unfold tailWord_2975059
  simp only [CollatzResearch.WordTrace]
  refine ⟨108509316128876817470432231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72339544085917878313621487 108509316128876817470432231)
  ·
    refine ⟨162763974193315226205648347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108509316128876817470432231 162763974193315226205648347)
    ·
      refine ⟨244145961289972839308472521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162763974193315226205648347 244145961289972839308472521)
      ·
        refine ⟨183109470967479629481354391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244145961289972839308472521 183109470967479629481354391)
        ·
          refine ⟨274664206451219444222031587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183109470967479629481354391 274664206451219444222031587)
          ·
            refine ⟨411996309676829166333047381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274664206451219444222031587 411996309676829166333047381)
            ·
              refine ⟨4828081754025341792965399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 411996309676829166333047381 4828081754025341792965399)
              ·
                refine ⟨7242122631038012689448099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4828081754025341792965399 7242122631038012689448099)
                ·
                  refine ⟨10863183946557019034172149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7242122631038012689448099 10863183946557019034172149)
                  ·
                    refine ⟨1018423494989720534453639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10863183946557019034172149 1018423494989720534453639)
                    ·
                      rfl

theorem cell22_2975059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 5].length) (baseStart_2975059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975059 prefixEnd_2975059 := by exact prefixLift 2975059
  have htrace : WordTrace (prefixWord ++ tailWord_2975059) baseStart_2975059 baseEnd_2975059 := by
    simpa [prefixWord, tailWord_2975059, baseEnd_2975059] using wordTrace_append hprefix tailTrace_2975059
  have hstable : (prefixWord ++ tailWord_2975059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975059).length < 2 ^ (prefixWord ++ tailWord_2975059).sum := by decide
  have hdescent : baseEnd_2975059 < baseStart_2975059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975080 : List Nat := [2, 1, 4, 2, 3, 2, 2, 1, 1, 4]
def baseStart_2975080 : Nat := 118140960795 + 2975080 * 2 ^ 59
def prefixEnd_2975080 : Nat := 4983230072969 + 3 ^ 40 * 2975080 * 2
def baseEnd_2975080 : Nat := 1018430683718883479678575

theorem tailTrace_2975080 : CollatzResearch.WordTrace tailWord_2975080 prefixEnd_2975080 1018430683718883479678575 := by
  unfold tailWord_2975080
  simp only [CollatzResearch.WordTrace]
  refine ⟨54255041030900369028473347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72340054707867158704631129 54255041030900369028473347)
  ·
    refine ⟨81382561546350553542710021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54255041030900369028473347 81382561546350553542710021)
    ·
      refine ⟨15259230289940728789258129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81382561546350553542710021 15259230289940728789258129)
      ·
        refine ⟨11444422717455546591943597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15259230289940728789258129 11444422717455546591943597)
        ·
          refine ⟨4291658519045829971978849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11444422717455546591943597 4291658519045829971978849)
          ·
            refine ⟨3218743889284372478984137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4291658519045829971978849 3218743889284372478984137)
            ·
              refine ⟨2414057916963279359238103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3218743889284372478984137 2414057916963279359238103)
              ·
                refine ⟨3621086875444919038857155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2414057916963279359238103 3621086875444919038857155)
                ·
                  refine ⟨5431630313167378558285733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3621086875444919038857155 5431630313167378558285733)
                  ·
                    refine ⟨1018430683718883479678575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5431630313167378558285733 1018430683718883479678575)
                    ·
                      rfl

theorem cell22_2975080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_2975080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975080 prefixEnd_2975080 := by exact prefixLift 2975080
  have htrace : WordTrace (prefixWord ++ tailWord_2975080) baseStart_2975080 baseEnd_2975080 := by
    simpa [prefixWord, tailWord_2975080, baseEnd_2975080] using wordTrace_append hprefix tailTrace_2975080
  have hstable : (prefixWord ++ tailWord_2975080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975080).length < 2 ^ (prefixWord ++ tailWord_2975080).sum := by decide
  have hdescent : baseEnd_2975080 < baseStart_2975080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975093 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 4, 3]
def baseStart_2975093 : Nat := 118140960795 + 2975093 * 2 ^ 59
def prefixEnd_2975093 : Nat := 4983230072969 + 3 ^ 40 * 2975093 * 2
def baseEnd_2975093 : Nat := 1018435133884555779103535

theorem tailTrace_2975093 : CollatzResearch.WordTrace tailWord_2975093 prefixEnd_2975093 1018435133884555779103535 := by
  unfold tailWord_2975093
  simp only [CollatzResearch.WordTrace]
  refine ⟨108510556210753641277169933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72340370807169094184779955 108510556210753641277169933)
  ·
    refine ⟨40691458579032615478938725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108510556210753641277169933 40691458579032615478938725)
    ·
      refine ⟨7629648483568615402301011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40691458579032615478938725 7629648483568615402301011)
      ·
        refine ⟨11444472725352923103451517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7629648483568615402301011 11444472725352923103451517)
        ·
          refine ⟨4291677272007346163794319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11444472725352923103451517 4291677272007346163794319)
          ·
            refine ⟨6437515908011019245691479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4291677272007346163794319 6437515908011019245691479)
            ·
              refine ⟨9656273862016528868537219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6437515908011019245691479 9656273862016528868537219)
              ·
                refine ⟨14484410793024793302805829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9656273862016528868537219 14484410793024793302805829)
                ·
                  refine ⟨2715827023692148744276093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14484410793024793302805829 2715827023692148744276093)
                  ·
                    refine ⟨1018435133884555779103535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2715827023692148744276093 1018435133884555779103535)
                    ·
                      rfl

theorem cell22_2975093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_2975093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975093 prefixEnd_2975093 := by exact prefixLift 2975093
  have htrace : WordTrace (prefixWord ++ tailWord_2975093) baseStart_2975093 baseEnd_2975093 := by
    simpa [prefixWord, tailWord_2975093, baseEnd_2975093] using wordTrace_append hprefix tailTrace_2975093
  have hstable : (prefixWord ++ tailWord_2975093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975093).length < 2 ^ (prefixWord ++ tailWord_2975093).sum := by decide
  have hdescent : baseEnd_2975093 < baseStart_2975093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975179 : List Nat := [1, 1, 1, 1, 3, 3, 2, 4, 6]
def baseStart_2975179 : Nat := 118140960795 + 2975179 * 2 ^ 59
def prefixEnd_2975179 : Nat := 4983230072969 + 3 ^ 40 * 2975179 * 2
def baseEnd_2975179 : Nat := 339488191147360073817757

theorem tailTrace_2975179 : CollatzResearch.WordTrace tailWord_2975179 prefixEnd_2975179 339488191147360073817757 := by
  unfold tailWord_2975179
  simp only [CollatzResearch.WordTrace]
  refine ⟨108513692888442077964800591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72342461925628051976533727 108513692888442077964800591)
  ·
    refine ⟨162770539332663116947200887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108513692888442077964800591 162770539332663116947200887)
    ·
      refine ⟨244155808998994675420801331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162770539332663116947200887 244155808998994675420801331)
      ·
        refine ⟨366233713498492013131201997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244155808998994675420801331 366233713498492013131201997)
        ·
          refine ⟨137337642561934504924200749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 366233713498492013131201997 137337642561934504924200749)
          ·
            refine ⟨51501615960725439346575281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137337642561934504924200749 51501615960725439346575281)
            ·
              refine ⟨38626211970544079509931461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51501615960725439346575281 38626211970544079509931461)
              ·
                refine ⟨7242414744477014908112149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38626211970544079509931461 7242414744477014908112149)
                ·
                  refine ⟨339488191147360073817757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7242414744477014908112149 339488191147360073817757)
                  ·
                    rfl

theorem cell22_2975179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 6].length) (baseStart_2975179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975179 prefixEnd_2975179 := by exact prefixLift 2975179
  have htrace : WordTrace (prefixWord ++ tailWord_2975179) baseStart_2975179 baseEnd_2975179 := by
    simpa [prefixWord, tailWord_2975179, baseEnd_2975179] using wordTrace_append hprefix tailTrace_2975179
  have hstable : (prefixWord ++ tailWord_2975179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975179).length < 2 ^ (prefixWord ++ tailWord_2975179).sum := by decide
  have hdescent : baseEnd_2975179 < baseStart_2975179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975228 : List Nat := [2, 2, 2, 1, 2, 1, 4, 3, 2, 3]
def baseStart_2975228 : Nat := 118140960795 + 2975228 * 2 ^ 59
def prefixEnd_2975228 : Nat := 4983230072969 + 3 ^ 40 * 2975228 * 2
def baseEnd_2975228 : Nat := 1018481347143460426978121

theorem tailTrace_2975228 : CollatzResearch.WordTrace tailWord_2975228 prefixEnd_2975228 1018481347143460426978121 := by
  unfold tailWord_2975228
  simp only [CollatzResearch.WordTrace]
  refine ⟨54257740032632279666667169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72343653376843039555556225 54257740032632279666667169)
  ·
    refine ⟨40693305024474209750000377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54257740032632279666667169 40693305024474209750000377)
    ·
      refine ⟨30519978768355657312500283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40693305024474209750000377 30519978768355657312500283)
      ·
        refine ⟨45779968152533485968750425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30519978768355657312500283 45779968152533485968750425)
        ·
          refine ⟨34334976114400114476562819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45779968152533485968750425 34334976114400114476562819)
          ·
            refine ⟨51502464171600171714844229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34334976114400114476562819 51502464171600171714844229)
            ·
              refine ⟨9656712032175032196533293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51502464171600171714844229 9656712032175032196533293)
              ·
                refine ⟨3621267012065637073699985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9656712032175032196533293 3621267012065637073699985)
                ·
                  refine ⟨2715950259049227805274989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3621267012065637073699985 2715950259049227805274989)
                  ·
                    refine ⟨1018481347143460426978121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2715950259049227805274989 1018481347143460426978121)
                    ·
                      rfl

theorem cell22_2975228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_2975228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975228 prefixEnd_2975228 := by exact prefixLift 2975228
  have htrace : WordTrace (prefixWord ++ tailWord_2975228) baseStart_2975228 baseEnd_2975228 := by
    simpa [prefixWord, tailWord_2975228, baseEnd_2975228] using wordTrace_append hprefix tailTrace_2975228
  have hstable : (prefixWord ++ tailWord_2975228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975228).length < 2 ^ (prefixWord ++ tailWord_2975228).sum := by decide
  have hdescent : baseEnd_2975228 < baseStart_2975228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975230 : List Nat := [4, 2, 2, 3, 1, 1, 1, 2, 6]
def baseStart_2975230 : Nat := 118140960795 + 2975230 * 2 ^ 59
def prefixEnd_2975230 : Nat := 4983230072969 + 3 ^ 40 * 2975230 * 2
def baseEnd_2975230 : Nat := 339494010594777696142705

theorem tailTrace_2975230 : CollatzResearch.WordTrace tailWord_2975230 prefixEnd_2975230 339494010594777696142705 := by
  unfold tailWord_2975230
  simp only [CollatzResearch.WordTrace]
  refine ⟨13564444126407164209363393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72343702007504875783271429 13564444126407164209363393)
  ·
    refine ⟨10173333094805373157022545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13564444126407164209363393 10173333094805373157022545)
    ·
      refine ⟨7629999821104029867766909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10173333094805373157022545 7629999821104029867766909)
      ·
        refine ⟨2861249932914011200412591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7629999821104029867766909 2861249932914011200412591)
        ·
          refine ⟨4291874899371016800618887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2861249932914011200412591 4291874899371016800618887)
          ·
            refine ⟨6437812349056525200928331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4291874899371016800618887 6437812349056525200928331)
            ·
              refine ⟨9656718523584787801392497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6437812349056525200928331 9656718523584787801392497)
              ·
                refine ⟨7242538892688590851044373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9656718523584787801392497 7242538892688590851044373)
                ·
                  refine ⟨339494010594777696142705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7242538892688590851044373 339494010594777696142705)
                  ·
                    rfl

theorem cell22_2975230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_2975230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975230 prefixEnd_2975230 := by exact prefixLift 2975230
  have htrace : WordTrace (prefixWord ++ tailWord_2975230) baseStart_2975230 baseEnd_2975230 := by
    simpa [prefixWord, tailWord_2975230, baseEnd_2975230] using wordTrace_append hprefix tailTrace_2975230
  have hstable : (prefixWord ++ tailWord_2975230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975230).length < 2 ^ (prefixWord ++ tailWord_2975230).sum := by decide
  have hdescent : baseEnd_2975230 < baseStart_2975230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975241 : List Nat := [1, 2, 1, 1, 3, 1, 7, 6]
def baseStart_2975241 : Nat := 118140960795 + 2975241 * 2 ^ 59
def prefixEnd_2975241 : Nat := 4983230072969 + 3 ^ 40 * 2975241 * 2
def baseEnd_2975241 : Nat := 113165088589903636267009

theorem tailTrace_2975241 : CollatzResearch.WordTrace tailWord_2975241 prefixEnd_2975241 113165088589903636267009 := by
  unfold tailWord_2975241
  simp only [CollatzResearch.WordTrace]
  refine ⟨108515954214217462553557577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72343969476144975035705051 108515954214217462553557577)
  ·
    refine ⟨81386965660663096915168183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108515954214217462553557577 81386965660663096915168183)
    ·
      refine ⟨122080448490994645372752275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81386965660663096915168183 122080448490994645372752275)
      ·
        refine ⟨183120672736491968059128413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122080448490994645372752275 183120672736491968059128413)
        ·
          refine ⟨68670252276184488022173155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183120672736491968059128413 68670252276184488022173155)
          ·
            refine ⟨103005378414276732033259733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68670252276184488022173155 103005378414276732033259733)
            ·
              refine ⟨2414188556584610907029525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 103005378414276732033259733 2414188556584610907029525)
              ·
                refine ⟨113165088589903636267009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2414188556584610907029525 113165088589903636267009)
                ·
                  rfl

theorem cell22_2975241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 6].length) (baseStart_2975241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975241 prefixEnd_2975241 := by exact prefixLift 2975241
  have htrace : WordTrace (prefixWord ++ tailWord_2975241) baseStart_2975241 baseEnd_2975241 := by
    simpa [prefixWord, tailWord_2975241, baseEnd_2975241] using wordTrace_append hprefix tailTrace_2975241
  have hstable : (prefixWord ++ tailWord_2975241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975241).length < 2 ^ (prefixWord ++ tailWord_2975241).sum := by decide
  have hdescent : baseEnd_2975241 < baseStart_2975241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975324 : List Nat := [2, 2, 4, 1, 2, 2, 3, 2, 1, 3]
def baseStart_2975324 : Nat := 118140960795 + 2975324 * 2 ^ 59
def prefixEnd_2975324 : Nat := 4983230072969 + 3 ^ 40 * 2975324 * 2
def baseEnd_2975324 : Nat := 1018514209905348176577827

theorem tailTrace_2975324 : CollatzResearch.WordTrace tailWord_2975324 prefixEnd_2975324 1018514209905348176577827 := by
  unfold tailWord_2975324
  simp only [CollatzResearch.WordTrace]
  refine ⟨54259490736458383864414513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72345987648611178485886017 54259490736458383864414513)
  ·
    refine ⟨40694618052343787898310885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54259490736458383864414513 40694618052343787898310885)
    ·
      refine ⟨7630240884814460230933291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40694618052343787898310885 7630240884814460230933291)
      ·
        refine ⟨11445361327221690346399937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7630240884814460230933291 11445361327221690346399937)
        ·
          refine ⟨8584020995416267759799953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11445361327221690346399937 8584020995416267759799953)
          ·
            refine ⟨6438015746562200819849965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8584020995416267759799953 6438015746562200819849965)
            ·
              refine ⟨2414255904960825307443737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6438015746562200819849965 2414255904960825307443737)
              ·
                refine ⟨1810691928720618980582803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2414255904960825307443737 1810691928720618980582803)
                ·
                  refine ⟨2716037893080928470874205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1810691928720618980582803 2716037893080928470874205)
                  ·
                    refine ⟨1018514209905348176577827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2716037893080928470874205 1018514209905348176577827)
                    ·
                      rfl

theorem cell22_2975324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_2975324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975324 prefixEnd_2975324 := by exact prefixLift 2975324
  have htrace : WordTrace (prefixWord ++ tailWord_2975324) baseStart_2975324 baseEnd_2975324 := by
    simpa [prefixWord, tailWord_2975324, baseEnd_2975324] using wordTrace_append hprefix tailTrace_2975324
  have hstable : (prefixWord ++ tailWord_2975324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975324).length < 2 ^ (prefixWord ++ tailWord_2975324).sum := by decide
  have hdescent : baseEnd_2975324 < baseStart_2975324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975350 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_2975350 : Nat := 118140960795 + 2975350 * 2 ^ 59
def prefixEnd_2975350 : Nat := 4983230072969 + 3 ^ 40 * 2975350 * 2
def baseEnd_2975350 : Nat := 1018523110236692775427747

theorem tailTrace_2975350 : CollatzResearch.WordTrace tailWord_2975350 prefixEnd_2975350 1018523110236692775427747 := by
  unfold tailWord_2975350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6782495610676410885579719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72346619847215049446183669 6782495610676410885579719)
  ·
    refine ⟨10173743416014616328369579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6782495610676410885579719 10173743416014616328369579)
    ·
      refine ⟨15260615124021924492554369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10173743416014616328369579 15260615124021924492554369)
      ·
        refine ⟨11445461343016443369415777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15260615124021924492554369 11445461343016443369415777)
        ·
          refine ⟨8584096007262332527061833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11445461343016443369415777 8584096007262332527061833)
          ·
            refine ⟨6438072005446749395296375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8584096007262332527061833 6438072005446749395296375)
            ·
              refine ⟨9657108008170124092944563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6438072005446749395296375 9657108008170124092944563)
              ·
                refine ⟨14485662012255186139416845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9657108008170124092944563 14485662012255186139416845)
                ·
                  refine ⟨5432123254595694802281317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14485662012255186139416845 5432123254595694802281317)
                  ·
                    refine ⟨1018523110236692775427747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5432123254595694802281317 1018523110236692775427747)
                    ·
                      rfl

theorem cell22_2975350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_2975350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975350 prefixEnd_2975350 := by exact prefixLift 2975350
  have htrace : WordTrace (prefixWord ++ tailWord_2975350) baseStart_2975350 baseEnd_2975350 := by
    simpa [prefixWord, tailWord_2975350, baseEnd_2975350] using wordTrace_append hprefix tailTrace_2975350
  have hstable : (prefixWord ++ tailWord_2975350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975350).length < 2 ^ (prefixWord ++ tailWord_2975350).sum := by decide
  have hdescent : baseEnd_2975350 < baseStart_2975350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975393 : List Nat := [1, 2, 3, 3, 2, 1, 3, 7]
def baseStart_2975393 : Nat := 118140960795 + 2975393 * 2 ^ 59
def prefixEnd_2975393 : Nat := 4983230072969 + 3 ^ 40 * 2975393 * 2
def baseEnd_2975393 : Nat := 113170870001717221844735

theorem tailTrace_2975393 : CollatzResearch.WordTrace tailWord_2975393 prefixEnd_2975393 113170870001717221844735 := by
  unfold tailWord_2975393
  simp only [CollatzResearch.WordTrace]
  refine ⟨108521498109666792513090833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72347665406444528342060555 108521498109666792513090833)
  ·
    refine ⟨81391123582250094384818125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108521498109666792513090833 81391123582250094384818125)
    ·
      refine ⟨30521671343343785394306797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81391123582250094384818125 30521671343343785394306797)
      ·
        refine ⟨11445626753753919522865049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30521671343343785394306797 11445626753753919522865049)
        ·
          refine ⟨8584220065315439642148787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11445626753753919522865049 8584220065315439642148787)
          ·
            refine ⟨12876330097973159463223181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8584220065315439642148787 12876330097973159463223181)
            ·
              refine ⟨4828623786739934798708693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12876330097973159463223181 4828623786739934798708693)
              ·
                refine ⟨113170870001717221844735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4828623786739934798708693 113170870001717221844735)
                ·
                  rfl

theorem cell22_2975393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 7].length) (baseStart_2975393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975393 prefixEnd_2975393 := by exact prefixLift 2975393
  have htrace : WordTrace (prefixWord ++ tailWord_2975393) baseStart_2975393 baseEnd_2975393 := by
    simpa [prefixWord, tailWord_2975393, baseEnd_2975393] using wordTrace_append hprefix tailTrace_2975393
  have hstable : (prefixWord ++ tailWord_2975393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975393).length < 2 ^ (prefixWord ++ tailWord_2975393).sum := by decide
  have hdescent : baseEnd_2975393 < baseStart_2975393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975408 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 5, 3]
def baseStart_2975408 : Nat := 118140960795 + 2975408 * 2 ^ 59
def prefixEnd_2975408 : Nat := 4983230072969 + 3 ^ 40 * 2975408 * 2
def baseEnd_2975408 : Nat := 1018542964821999957477569

theorem tailTrace_2975408 : CollatzResearch.WordTrace tailWord_2975408 prefixEnd_2975408 1018542964821999957477569 := by
  unfold tailWord_2975408
  simp only [CollatzResearch.WordTrace]
  refine ⟨54261022602306225037443439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72348030136408300049924585 54261022602306225037443439)
  ·
    refine ⟨81391533903459337556165159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54261022602306225037443439 81391533903459337556165159)
    ·
      refine ⟨122087300855189006334247739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81391533903459337556165159 122087300855189006334247739)
      ·
        refine ⟨183130951282783509501371609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122087300855189006334247739 183130951282783509501371609)
        ·
          refine ⟨137348213462087632126028707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183130951282783509501371609 137348213462087632126028707)
          ·
            refine ⟨206022320193131448189043061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137348213462087632126028707 206022320193131448189043061)
            ·
              refine ⟨19314592518106073267722787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 206022320193131448189043061 19314592518106073267722787)
              ·
                refine ⟨28971888777159109901584181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19314592518106073267722787 28971888777159109901584181)
                ·
                  refine ⟨2716114572858666553273517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28971888777159109901584181 2716114572858666553273517)
                  ·
                    refine ⟨1018542964821999957477569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2716114572858666553273517 1018542964821999957477569)
                    ·
                      rfl

theorem cell22_2975408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 5, 3].length) (baseStart_2975408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975408 prefixEnd_2975408 := by exact prefixLift 2975408
  have htrace : WordTrace (prefixWord ++ tailWord_2975408) baseStart_2975408 baseEnd_2975408 := by
    simpa [prefixWord, tailWord_2975408, baseEnd_2975408] using wordTrace_append hprefix tailTrace_2975408
  have hstable : (prefixWord ++ tailWord_2975408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975408).length < 2 ^ (prefixWord ++ tailWord_2975408).sum := by decide
  have hdescent : baseEnd_2975408 < baseStart_2975408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975438 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 7]
def baseStart_2975438 : Nat := 118140960795 + 2975438 * 2 ^ 59
def prefixEnd_2975438 : Nat := 4983230072969 + 3 ^ 40 * 2975438 * 2
def baseEnd_2975438 : Nat := 339517744811696626409159

theorem tailTrace_2975438 : CollatzResearch.WordTrace tailWord_2975438 prefixEnd_2975438 339517744811696626409159 := by
  unfold tailWord_2975438
  simp only [CollatzResearch.WordTrace]
  refine ⟨13565392424312970649809871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72348759596335843465652645 13565392424312970649809871)
  ·
    refine ⟨20348088636469455974714807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13565392424312970649809871 20348088636469455974714807)
    ·
      refine ⟨30522132954704183962072211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20348088636469455974714807 30522132954704183962072211)
      ·
        refine ⟨45783199432056275943108317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30522132954704183962072211 45783199432056275943108317)
        ·
          refine ⟨17168699787021103478665619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45783199432056275943108317 17168699787021103478665619)
          ·
            refine ⟨25753049680531655217998429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17168699787021103478665619 25753049680531655217998429)
            ·
              refine ⟨9657393630199370706749411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25753049680531655217998429 9657393630199370706749411)
              ·
                refine ⟨14486090445299056060124117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9657393630199370706749411 14486090445299056060124117)
                ·
                  refine ⟨339517744811696626409159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14486090445299056060124117 339517744811696626409159)
                  ·
                    rfl

theorem cell22_2975438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_2975438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975438 prefixEnd_2975438 := by exact prefixLift 2975438
  have htrace : WordTrace (prefixWord ++ tailWord_2975438) baseStart_2975438 baseEnd_2975438 := by
    simpa [prefixWord, tailWord_2975438, baseEnd_2975438] using wordTrace_append hprefix tailTrace_2975438
  have hstable : (prefixWord ++ tailWord_2975438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975438).length < 2 ^ (prefixWord ++ tailWord_2975438).sum := by decide
  have hdescent : baseEnd_2975438 < baseStart_2975438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975442 : List Nat := [3, 2, 2, 2, 2, 2, 2, 1, 3, 3]
def baseStart_2975442 : Nat := 118140960795 + 2975442 * 2 ^ 59
def prefixEnd_2975442 : Nat := 4983230072969 + 3 ^ 40 * 2975442 * 2
def baseEnd_2975442 : Nat := 1018554603716835202127465

theorem tailTrace_2975442 : CollatzResearch.WordTrace tailWord_2975442 prefixEnd_2975442 1018554603716835202127465 := by
  unfold tailWord_2975442
  simp only [CollatzResearch.WordTrace]
  refine ⟨27130821321622318470406145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72348856857659515921083053 27130821321622318470406145)
  ·
    refine ⟨20348115991216738852804609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27130821321622318470406145 20348115991216738852804609)
    ·
      refine ⟨15261086993412554139603457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20348115991216738852804609 15261086993412554139603457)
      ·
        refine ⟨11445815245059415604702593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15261086993412554139603457 11445815245059415604702593)
        ·
          refine ⟨8584361433794561703526945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11445815245059415604702593 8584361433794561703526945)
          ·
            refine ⟨6438271075345921277645209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8584361433794561703526945 6438271075345921277645209)
            ·
              refine ⟨4828703306509440958233907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6438271075345921277645209 4828703306509440958233907)
              ·
                refine ⟨7243054959764161437350861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4828703306509440958233907 7243054959764161437350861)
                ·
                  refine ⟨2716145609911560539006573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7243054959764161437350861 2716145609911560539006573)
                  ·
                    refine ⟨1018554603716835202127465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2716145609911560539006573 1018554603716835202127465)
                    ·
                      rfl

theorem cell22_2975442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_2975442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975442 prefixEnd_2975442 := by exact prefixLift 2975442
  have htrace : WordTrace (prefixWord ++ tailWord_2975442) baseStart_2975442 baseEnd_2975442 := by
    simpa [prefixWord, tailWord_2975442, baseEnd_2975442] using wordTrace_append hprefix tailTrace_2975442
  have hstable : (prefixWord ++ tailWord_2975442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975442).length < 2 ^ (prefixWord ++ tailWord_2975442).sum := by decide
  have hdescent : baseEnd_2975442 < baseStart_2975442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975455 : List Nat := [1, 1, 2, 3, 2, 2, 5, 1, 5]
def baseStart_2975455 : Nat := 118140960795 + 2975455 * 2 ^ 59
def prefixEnd_2975455 : Nat := 4983230072969 + 3 ^ 40 * 2975455 * 2
def baseEnd_2975455 : Nat := 339519684627502500517475

theorem tailTrace_2975455 : CollatzResearch.WordTrace tailWord_2975455 prefixEnd_2975455 339519684627502500517475 := by
  unfold tailWord_2975455
  simp only [CollatzResearch.WordTrace]
  refine ⟨108523759435442177101847819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72349172956961451401231879 108523759435442177101847819)
  ·
    refine ⟨162785639153163265652771729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108523759435442177101847819 162785639153163265652771729)
    ·
      refine ⟨122089229364872449239578797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162785639153163265652771729 122089229364872449239578797)
      ·
        refine ⟨45783461011827168464842049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122089229364872449239578797 45783461011827168464842049)
        ·
          refine ⟨34337595758870376348631537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45783461011827168464842049 34337595758870376348631537)
          ·
            refine ⟨25753196819152782261473653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34337595758870376348631537 25753196819152782261473653)
            ·
              refine ⟨2414362201795573337013155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25753196819152782261473653 2414362201795573337013155)
              ·
                refine ⟨3621543302693360005519733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2414362201795573337013155 3621543302693360005519733)
                ·
                  refine ⟨339519684627502500517475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3621543302693360005519733 339519684627502500517475)
                  ·
                    rfl

theorem cell22_2975455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 5].length) (baseStart_2975455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975455 prefixEnd_2975455 := by exact prefixLift 2975455
  have htrace : WordTrace (prefixWord ++ tailWord_2975455) baseStart_2975455 baseEnd_2975455 := by
    simpa [prefixWord, tailWord_2975455, baseEnd_2975455] using wordTrace_append hprefix tailTrace_2975455
  have hstable : (prefixWord ++ tailWord_2975455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975455).length < 2 ^ (prefixWord ++ tailWord_2975455).sum := by decide
  have hdescent : baseEnd_2975455 < baseStart_2975455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975468 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 3, 4]
def baseStart_2975468 : Nat := 118140960795 + 2975468 * 2 ^ 59
def prefixEnd_2975468 : Nat := 4983230072969 + 3 ^ 40 * 2975468 * 2
def baseEnd_2975468 : Nat := 1018563504048179800977385

theorem tailTrace_2975468 : CollatzResearch.WordTrace tailWord_2975468 prefixEnd_2975468 1018563504048179800977385 := by
  unfold tailWord_2975468
  simp only [CollatzResearch.WordTrace]
  refine ⟨54262116792197540161035529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72349489056263386881380705 54262116792197540161035529)
  ·
    refine ⟨40696587594148155120776647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54262116792197540161035529 40696587594148155120776647)
    ·
      refine ⟨61044881391222232681164971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40696587594148155120776647 61044881391222232681164971)
      ·
        refine ⟨91567322086833349021747457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61044881391222232681164971 91567322086833349021747457)
        ·
          refine ⟨68675491565125011766310593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91567322086833349021747457 68675491565125011766310593)
          ·
            refine ⟨51506618673843758824732945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68675491565125011766310593 51506618673843758824732945)
            ·
              refine ⟨38629964005382819118549709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51506618673843758824732945 38629964005382819118549709)
              ·
                refine ⟨14486236502018557169456141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38629964005382819118549709 14486236502018557169456141)
                ·
                  refine ⟨5432338688256958938546053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14486236502018557169456141 5432338688256958938546053)
                  ·
                    refine ⟨1018563504048179800977385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5432338688256958938546053 1018563504048179800977385)
                    ·
                      rfl

theorem cell22_2975468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_2975468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975468 prefixEnd_2975468 := by exact prefixLift 2975468
  have htrace : WordTrace (prefixWord ++ tailWord_2975468) baseStart_2975468 baseEnd_2975468 := by
    simpa [prefixWord, tailWord_2975468, baseEnd_2975468] using wordTrace_append hprefix tailTrace_2975468
  have hstable : (prefixWord ++ tailWord_2975468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975468).length < 2 ^ (prefixWord ++ tailWord_2975468).sum := by decide
  have hdescent : baseEnd_2975468 < baseStart_2975468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975500 : List Nat := [2, 2, 1, 2, 2, 1, 2, 6, 4]
def baseStart_2975500 : Nat := 118140960795 + 2975500 * 2 ^ 59
def prefixEnd_2975500 : Nat := 4983230072969 + 3 ^ 40 * 2975500 * 2
def baseEnd_2975500 : Nat := 339524819434047461392429

theorem tailTrace_2975500 : CollatzResearch.WordTrace tailWord_2975500 prefixEnd_2975500 339524819434047461392429 := by
  unfold tailWord_2975500
  simp only [CollatzResearch.WordTrace]
  refine ⟨54262700360139574893617977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72350267146852766524823969 54262700360139574893617977)
  ·
    refine ⟨40697025270104681170213483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54262700360139574893617977 40697025270104681170213483)
    ·
      refine ⟨61045537905157021755320225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40697025270104681170213483 61045537905157021755320225)
      ·
        refine ⟨45784153428867766316490169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61045537905157021755320225 45784153428867766316490169)
        ·
          refine ⟨34338115071650824737367627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45784153428867766316490169 34338115071650824737367627)
          ·
            refine ⟨51507172607476237106051441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34338115071650824737367627 51507172607476237106051441)
            ·
              refine ⟨38630379455607177829538581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51507172607476237106051441 38630379455607177829538581)
              ·
                refine ⟨1810799036981586460759621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38630379455607177829538581 1810799036981586460759621)
                ·
                  refine ⟨339524819434047461392429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1810799036981586460759621 339524819434047461392429)
                  ·
                    rfl

theorem cell22_2975500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_2975500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975500 prefixEnd_2975500 := by exact prefixLift 2975500
  have htrace : WordTrace (prefixWord ++ tailWord_2975500) baseStart_2975500 baseEnd_2975500 := by
    simpa [prefixWord, tailWord_2975500, baseEnd_2975500] using wordTrace_append hprefix tailTrace_2975500
  have hstable : (prefixWord ++ tailWord_2975500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975500).length < 2 ^ (prefixWord ++ tailWord_2975500).sum := by decide
  have hdescent : baseEnd_2975500 < baseStart_2975500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975515 : List Nat := [1, 1, 1, 1, 1, 1, 4, 7, 2, 3]
def baseStart_2975515 : Nat := 118140960795 + 2975515 * 2 ^ 59
def prefixEnd_2975515 : Nat := 4983230072969 + 3 ^ 40 * 2975515 * 2
def baseEnd_2975515 : Nat := 1018579593108687345052241

theorem tailTrace_2975515 : CollatzResearch.WordTrace tailWord_2975515 prefixEnd_2975515 1018579593108687345052241 := by
  unfold tailWord_2975515
  simp only [CollatzResearch.WordTrace]
  refine ⟨108525947815224807349031999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72350631876816538232687999 108525947815224807349031999)
  ·
    refine ⟨162788921722837211023547999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108525947815224807349031999 162788921722837211023547999)
    ·
      refine ⟨244183382584255816535321999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162788921722837211023547999 244183382584255816535321999)
      ·
        refine ⟨366275073876383724802982999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244183382584255816535321999 366275073876383724802982999)
        ·
          refine ⟨549412610814575587204474499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366275073876383724802982999 549412610814575587204474499)
          ·
            refine ⟨824118916221863380806711749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549412610814575587204474499 824118916221863380806711749)
            ·
              refine ⟨154522296791599383901258453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 824118916221863380806711749 154522296791599383901258453)
              ·
                refine ⟨3621616331053110560185745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 154522296791599383901258453 3621616331053110560185745)
                ·
                  refine ⟨2716212248289832920139309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3621616331053110560185745 2716212248289832920139309)
                  ·
                    refine ⟨1018579593108687345052241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2716212248289832920139309 1018579593108687345052241)
                    ·
                      rfl

theorem cell22_2975515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 3].length) (baseStart_2975515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975515 prefixEnd_2975515 := by exact prefixLift 2975515
  have htrace : WordTrace (prefixWord ++ tailWord_2975515) baseStart_2975515 baseEnd_2975515 := by
    simpa [prefixWord, tailWord_2975515, baseEnd_2975515] using wordTrace_append hprefix tailTrace_2975515
  have hstable : (prefixWord ++ tailWord_2975515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975515).length < 2 ^ (prefixWord ++ tailWord_2975515).sum := by decide
  have hdescent : baseEnd_2975515 < baseStart_2975515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975545 : List Nat := [1, 2, 1, 7, 1, 10]
def baseStart_2975545 : Nat := 118140960795 + 2975545 * 2 ^ 59
def prefixEnd_2975545 : Nat := 4983230072969 + 3 ^ 40 * 2975545 * 2
def baseEnd_2975545 : Nat := 12575183490392311935829

theorem tailTrace_2975545 : CollatzResearch.WordTrace tailWord_2975545 prefixEnd_2975545 12575183490392311935829 := by
  unfold tailWord_2975545
  simp only [CollatzResearch.WordTrace]
  refine ⟨108527042005116122472624089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72351361336744081648416059 108527042005116122472624089)
  ·
    refine ⟨81395281503837091854468067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108527042005116122472624089 81395281503837091854468067)
    ·
      refine ⟨122092922255755637781702101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81395281503837091854468067 122092922255755637781702101)
      ·
        refine ⟨2861552865369272760508643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 122092922255755637781702101 2861552865369272760508643)
        ·
          refine ⟨4292329298053909140762965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2861552865369272760508643 4292329298053909140762965)
          ·
            refine ⟨12575183490392311935829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4292329298053909140762965 12575183490392311935829)
            ·
              rfl

theorem cell22_2975545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 10].length) (baseStart_2975545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975545 prefixEnd_2975545 := by exact prefixLift 2975545
  have htrace : WordTrace (prefixWord ++ tailWord_2975545) baseStart_2975545 baseEnd_2975545 := by
    simpa [prefixWord, tailWord_2975545, baseEnd_2975545] using wordTrace_append hprefix tailTrace_2975545
  have hstable : (prefixWord ++ tailWord_2975545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975545).length < 2 ^ (prefixWord ++ tailWord_2975545).sum := by decide
  have hdescent : baseEnd_2975545 < baseStart_2975545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975549 : List Nat := [1, 4, 1, 4, 1, 2, 2, 2, 2, 3]
def baseStart_2975549 : Nat := 118140960795 + 2975549 * 2 ^ 59
def prefixEnd_2975549 : Nat := 4983230072969 + 3 ^ 40 * 2975549 * 2
def baseEnd_2975549 : Nat := 1018591232003522589702137

theorem tailTrace_2975549 : CollatzResearch.WordTrace tailWord_2975549 prefixEnd_2975549 1018591232003522589702137 := by
  unfold tailWord_2975549
  simp only [CollatzResearch.WordTrace]
  refine ⟨108527187897101631155769701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72351458598067754103846467 108527187897101631155769701)
  ·
    refine ⟨20348847730706555841706819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108527187897101631155769701 20348847730706555841706819)
    ·
      refine ⟨30523271596059833762560229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20348847730706555841706819 30523271596059833762560229)
      ·
        refine ⟨5723113424261218830480043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30523271596059833762560229 5723113424261218830480043)
        ·
          refine ⟨8584670136391828245720065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5723113424261218830480043 8584670136391828245720065)
          ·
            refine ⟨6438502602293871184290049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8584670136391828245720065 6438502602293871184290049)
            ·
              refine ⟨4828876951720403388217537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6438502602293871184290049 4828876951720403388217537)
              ·
                refine ⟨3621657713790302541163153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4828876951720403388217537 3621657713790302541163153)
                ·
                  refine ⟨2716243285342726905872365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3621657713790302541163153 2716243285342726905872365)
                  ·
                    refine ⟨1018591232003522589702137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2716243285342726905872365 1018591232003522589702137)
                    ·
                      rfl

theorem cell22_2975549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_2975549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975549 prefixEnd_2975549 := by exact prefixLift 2975549
  have htrace : WordTrace (prefixWord ++ tailWord_2975549) baseStart_2975549 baseEnd_2975549 := by
    simpa [prefixWord, tailWord_2975549, baseEnd_2975549] using wordTrace_append hprefix tailTrace_2975549
  have hstable : (prefixWord ++ tailWord_2975549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975549).length < 2 ^ (prefixWord ++ tailWord_2975549).sum := by decide
  have hdescent : baseEnd_2975549 < baseStart_2975549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975551 : List Nat := [1, 1, 2, 2, 7, 1, 2, 2, 4]
def baseStart_2975551 : Nat := 118140960795 + 2975551 * 2 ^ 59
def prefixEnd_2975551 : Nat := 4983230072969 + 3 ^ 40 * 2975551 * 2
def baseEnd_2975551 : Nat := 339530638881465083717377

theorem tailTrace_2975551 : CollatzResearch.WordTrace tailWord_2975551 prefixEnd_2975551 339530638881465083717377 := by
  unfold tailWord_2975551
  simp only [CollatzResearch.WordTrace]
  refine ⟨108527260843094385497342507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72351507228729590331561671 108527260843094385497342507)
  ·
    refine ⟨162790891264641578246013761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108527260843094385497342507 162790891264641578246013761)
    ·
      refine ⟨122093168448481183684510321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162790891264641578246013761 122093168448481183684510321)
      ·
        refine ⟨91569876336360887763382741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122093168448481183684510321 91569876336360887763382741)
        ·
          refine ⟨2146168976633458306954283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 91569876336360887763382741 2146168976633458306954283)
          ·
            refine ⟨3219253464950187460431425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2146168976633458306954283 3219253464950187460431425)
            ·
              refine ⟨2414440098712640595323569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3219253464950187460431425 2414440098712640595323569)
              ·
                refine ⟨1810830074034480446492677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2414440098712640595323569 1810830074034480446492677)
                ·
                  refine ⟨339530638881465083717377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1810830074034480446492677 339530638881465083717377)
                  ·
                    rfl

theorem cell22_2975551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 4].length) (baseStart_2975551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975551 prefixEnd_2975551 := by exact prefixLift 2975551
  have htrace : WordTrace (prefixWord ++ tailWord_2975551) baseStart_2975551 baseEnd_2975551 := by
    simpa [prefixWord, tailWord_2975551, baseEnd_2975551] using wordTrace_append hprefix tailTrace_2975551
  have hstable : (prefixWord ++ tailWord_2975551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975551).length < 2 ^ (prefixWord ++ tailWord_2975551).sum := by decide
  have hdescent : baseEnd_2975551 < baseStart_2975551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975605 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 4, 5]
def baseStart_2975605 : Nat := 118140960795 + 2975605 * 2 ^ 59
def prefixEnd_2975605 : Nat := 4983230072969 + 3 ^ 40 * 2975605 * 2
def baseEnd_2975605 : Nat := 1018610401947957110301965

theorem tailTrace_2975605 : CollatzResearch.WordTrace tailWord_2975605 prefixEnd_2975605 1018610401947957110301965 := by
  unfold tailWord_2975605
  simp only [CollatzResearch.WordTrace]
  refine ⟨108529230384898752719808269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72352820256599168479872179 108529230384898752719808269)
  ·
    refine ⟨40698461394337032269928101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108529230384898752719808269 40698461394337032269928101)
    ·
      refine ⟨7630961511438193550611519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40698461394337032269928101 7630961511438193550611519)
      ·
        refine ⟨11446442267157290325917279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7630961511438193550611519 11446442267157290325917279)
        ·
          refine ⟨17169663400735935488875919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11446442267157290325917279 17169663400735935488875919)
          ·
            refine ⟨25754495101103903233313879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17169663400735935488875919 25754495101103903233313879)
            ·
              refine ⟨38631742651655854849970819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25754495101103903233313879 38631742651655854849970819)
              ·
                refine ⟨57947613977483782274956229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38631742651655854849970819 57947613977483782274956229)
                ·
                  refine ⟨10865177620778209176554293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57947613977483782274956229 10865177620778209176554293)
                  ·
                    refine ⟨1018610401947957110301965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10865177620778209176554293 1018610401947957110301965)
                    ·
                      rfl

theorem cell22_2975605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_2975605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975605 prefixEnd_2975605 := by exact prefixLift 2975605
  have htrace : WordTrace (prefixWord ++ tailWord_2975605) baseStart_2975605 baseEnd_2975605 := by
    simpa [prefixWord, tailWord_2975605, baseEnd_2975605] using wordTrace_append hprefix tailTrace_2975605
  have hstable : (prefixWord ++ tailWord_2975605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975605).length < 2 ^ (prefixWord ++ tailWord_2975605).sum := by decide
  have hdescent : baseEnd_2975605 < baseStart_2975605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975620 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_2975620 : Nat := 118140960795 + 2975620 * 2 ^ 59
def prefixEnd_2975620 : Nat := 4983230072969 + 3 ^ 40 * 2975620 * 2
def baseEnd_2975620 : Nat := 1018615536754502071176919

theorem tailTrace_2975620 : CollatzResearch.WordTrace tailWord_2975620 prefixEnd_2975620 1018615536754502071176919 := by
  unfold tailWord_2975620
  simp only [CollatzResearch.WordTrace]
  refine ⟨54264888739922205140802157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72353184986562940187736209 54264888739922205140802157)
  ·
    refine ⟨20349333277470826927800809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54264888739922205140802157 20349333277470826927800809)
    ·
      refine ⟨15261999958103120195850607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20349333277470826927800809 15261999958103120195850607)
      ·
        refine ⟨22892999937154680293775911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15261999958103120195850607 22892999937154680293775911)
        ·
          refine ⟨34339499905732020440663867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22892999937154680293775911 34339499905732020440663867)
          ·
            refine ⟨51509249858598030660995801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34339499905732020440663867 51509249858598030660995801)
            ·
              refine ⟨38631937393948522995746851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51509249858598030660995801 38631937393948522995746851)
              ·
                refine ⟨57947906090922784493620277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38631937393948522995746851 57947906090922784493620277)
                ·
                  refine ⟨5432616196024011046276901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57947906090922784493620277 5432616196024011046276901)
                  ·
                    refine ⟨1018615536754502071176919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5432616196024011046276901 1018615536754502071176919)
                    ·
                      rfl

theorem cell22_2975620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_2975620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975620 prefixEnd_2975620 := by exact prefixLift 2975620
  have htrace : WordTrace (prefixWord ++ tailWord_2975620) baseStart_2975620 baseEnd_2975620 := by
    simpa [prefixWord, tailWord_2975620, baseEnd_2975620] using wordTrace_append hprefix tailTrace_2975620
  have hstable : (prefixWord ++ tailWord_2975620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975620).length < 2 ^ (prefixWord ++ tailWord_2975620).sum := by decide
  have hdescent : baseEnd_2975620 < baseStart_2975620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975624 : List Nat := [2, 1, 3, 3, 3, 1, 3, 1, 5]
def baseStart_2975624 : Nat := 118140960795 + 2975624 * 2 ^ 59
def prefixEnd_2975624 : Nat := 4983230072969 + 3 ^ 40 * 2975624 * 2
def baseEnd_2975624 : Nat := 339538968678749131358969

theorem tailTrace_2975624 : CollatzResearch.WordTrace tailWord_2975624 prefixEnd_2975624 339538968678749131358969 := by
  unfold tailWord_2975624
  simp only [CollatzResearch.WordTrace]
  refine ⟨54264961685914959482374963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72353282247886612643166617 54264961685914959482374963)
  ·
    refine ⟨81397442528872439223562445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54264961685914959482374963 81397442528872439223562445)
    ·
      refine ⟨30524040948327164708835917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81397442528872439223562445 30524040948327164708835917)
      ·
        refine ⟨11446515355622686765813469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30524040948327164708835917 11446515355622686765813469)
        ·
          refine ⟨4292443258358507537180051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11446515355622686765813469 4292443258358507537180051)
          ·
            refine ⟨6438664887537761305770077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4292443258358507537180051 6438664887537761305770077)
            ·
              refine ⟨2414499332826660489663779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6438664887537761305770077 2414499332826660489663779)
              ·
                refine ⟨3621748999239990734495669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2414499332826660489663779 3621748999239990734495669)
                ·
                  refine ⟨339538968678749131358969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3621748999239990734495669 339538968678749131358969)
                  ·
                    rfl

theorem cell22_2975624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 5].length) (baseStart_2975624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975624 prefixEnd_2975624 := by exact prefixLift 2975624
  have htrace : WordTrace (prefixWord ++ tailWord_2975624) baseStart_2975624 baseEnd_2975624 := by
    simpa [prefixWord, tailWord_2975624, baseEnd_2975624] using wordTrace_append hprefix tailTrace_2975624
  have hstable : (prefixWord ++ tailWord_2975624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975624).length < 2 ^ (prefixWord ++ tailWord_2975624).sum := by decide
  have hdescent : baseEnd_2975624 < baseStart_2975624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975637 : List Nat := [1, 3, 2, 1, 1, 3, 4, 2, 1, 4]
def baseStart_2975637 : Nat := 118140960795 + 2975637 * 2 ^ 59
def prefixEnd_2975637 : Nat := 4983230072969 + 3 ^ 40 * 2975637 * 2
def baseEnd_2975637 : Nat := 1018621356201919693501867

theorem tailTrace_2975637 : CollatzResearch.WordTrace tailWord_2975637 prefixEnd_2975637 1018621356201919693501867 := by
  unfold tailWord_2975637
  simp only [CollatzResearch.WordTrace]
  refine ⟨108530397520782822184973165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72353598347188548123315443 108530397520782822184973165)
  ·
    refine ⟨40698899070293558319364937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108530397520782822184973165 40698899070293558319364937)
    ·
      refine ⟨30524174302720168739523703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40698899070293558319364937 30524174302720168739523703)
      ·
        refine ⟨45786261454080253109285555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30524174302720168739523703 45786261454080253109285555)
        ·
          refine ⟨68679392181120379663928333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45786261454080253109285555 68679392181120379663928333)
          ·
            refine ⟨25754772067920142373973125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68679392181120379663928333 25754772067920142373973125)
            ·
              refine ⟨4829019762735026695119961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25754772067920142373973125 4829019762735026695119961)
              ·
                refine ⟨3621764822051270021339971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4829019762735026695119961 3621764822051270021339971)
                ·
                  refine ⟨5432647233076905032009957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3621764822051270021339971 5432647233076905032009957)
                  ·
                    refine ⟨1018621356201919693501867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5432647233076905032009957 1018621356201919693501867)
                    ·
                      rfl

theorem cell22_2975637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_2975637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975637 prefixEnd_2975637 := by exact prefixLift 2975637
  have htrace : WordTrace (prefixWord ++ tailWord_2975637) baseStart_2975637 baseEnd_2975637 := by
    simpa [prefixWord, tailWord_2975637, baseEnd_2975637] using wordTrace_append hprefix tailTrace_2975637
  have hstable : (prefixWord ++ tailWord_2975637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975637).length < 2 ^ (prefixWord ++ tailWord_2975637).sum := by decide
  have hdescent : baseEnd_2975637 < baseStart_2975637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975662 : List Nat := [4, 1, 5, 1, 1, 1, 3, 2, 1, 3]
def baseStart_2975662 : Nat := 118140960795 + 2975662 * 2 ^ 59
def prefixEnd_2975662 : Nat := 4983230072969 + 3 ^ 40 * 2975662 * 2
def baseEnd_2975662 : Nat := 1018629914212827961626791

theorem tailTrace_2975662 : CollatzResearch.WordTrace tailWord_2975662 prefixEnd_2975662 1018629914212827961626791 := by
  unfold tailWord_2975662
  simp only [CollatzResearch.WordTrace]
  refine ⟨13566413668211531431829155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72354206230461500969755493 13566413668211531431829155)
  ·
    refine ⟨20349620502317297147743733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13566413668211531431829155 20349620502317297147743733)
    ·
      refine ⟨1907776922092246607600975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20349620502317297147743733 1907776922092246607600975)
      ·
        refine ⟨2861665383138369911401463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1907776922092246607600975 2861665383138369911401463)
        ·
          refine ⟨4292498074707554867102195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2861665383138369911401463 4292498074707554867102195)
          ·
            refine ⟨6438747112061332300653293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4292498074707554867102195 6438747112061332300653293)
            ·
              refine ⟨2414530167022999612744985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6438747112061332300653293 2414530167022999612744985)
              ·
                refine ⟨1810897625267249709558739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2414530167022999612744985 1810897625267249709558739)
                ·
                  refine ⟨2716346437900874564338109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1810897625267249709558739 2716346437900874564338109)
                  ·
                    refine ⟨1018629914212827961626791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2716346437900874564338109 1018629914212827961626791)
                    ·
                      rfl

theorem cell22_2975662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_2975662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975662 prefixEnd_2975662 := by exact prefixLift 2975662
  have htrace : WordTrace (prefixWord ++ tailWord_2975662) baseStart_2975662 baseEnd_2975662 := by
    simpa [prefixWord, tailWord_2975662, baseEnd_2975662] using wordTrace_append hprefix tailTrace_2975662
  have hstable : (prefixWord ++ tailWord_2975662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975662).length < 2 ^ (prefixWord ++ tailWord_2975662).sum := by decide
  have hdescent : baseEnd_2975662 < baseStart_2975662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975667 : List Nat := [1, 1, 1, 2, 3, 1, 4, 4, 2, 3]
def baseStart_2975667 : Nat := 118140960795 + 2975667 * 2 ^ 59
def prefixEnd_2975667 : Nat := 4983230072969 + 3 ^ 40 * 2975667 * 2
def baseEnd_2975667 : Nat := 1018631625815009615251775

theorem tailTrace_2975667 : CollatzResearch.WordTrace tailWord_2975667 prefixEnd_2975667 1018631625815009615251775 := by
  unfold tailWord_2975667
  simp only [CollatzResearch.WordTrace]
  refine ⟨108531491710674137308565255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72354327807116091539043503 108531491710674137308565255)
  ·
    refine ⟨162797237566011205962847883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108531491710674137308565255 162797237566011205962847883)
    ·
      refine ⟨244195856349016808944271825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162797237566011205962847883 244195856349016808944271825)
      ·
        refine ⟨183146892261762606708203869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244195856349016808944271825 183146892261762606708203869)
        ·
          refine ⟨68680084598160977515576451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183146892261762606708203869 68680084598160977515576451)
          ·
            refine ⟨103020126897241466273364677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68680084598160977515576451 103020126897241466273364677)
            ·
              refine ⟨19316273793232774926255877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103020126897241466273364677 19316273793232774926255877)
              ·
                refine ⟨3621801336231145298672977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19316273793232774926255877 3621801336231145298672977)
                ·
                  refine ⟨2716351002173358974004733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3621801336231145298672977 2716351002173358974004733)
                  ·
                    refine ⟨1018631625815009615251775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2716351002173358974004733 1018631625815009615251775)
                    ·
                      rfl

theorem cell22_2975667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 3].length) (baseStart_2975667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975667 prefixEnd_2975667 := by exact prefixLift 2975667
  have htrace : WordTrace (prefixWord ++ tailWord_2975667) baseStart_2975667 baseEnd_2975667 := by
    simpa [prefixWord, tailWord_2975667, baseEnd_2975667] using wordTrace_append hprefix tailTrace_2975667
  have hstable : (prefixWord ++ tailWord_2975667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975667).length < 2 ^ (prefixWord ++ tailWord_2975667).sum := by decide
  have hdescent : baseEnd_2975667 < baseStart_2975667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975680 : List Nat := [2, 1, 1, 2, 3, 2, 4, 7]
def baseStart_2975680 : Nat := 118140960795 + 2975680 * 2 ^ 59
def prefixEnd_2975680 : Nat := 4983230072969 + 3 ^ 40 * 2975680 * 2
def baseEnd_2975680 : Nat := 113181786220075768297415

theorem tailTrace_2975680 : CollatzResearch.WordTrace tailWord_2975680 prefixEnd_2975680 113181786220075768297415 := by
  unfold tailWord_2975680
  simp only [CollatzResearch.WordTrace]
  refine ⟨54265982929813520264394247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72354643906418027019192329 54265982929813520264394247)
  ·
    refine ⟨81398974394720280396591371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54265982929813520264394247 81398974394720280396591371)
    ·
      refine ⟨122098461592080420594887057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81398974394720280396591371 122098461592080420594887057)
      ·
        refine ⟨91573846194060315446165293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122098461592080420594887057 91573846194060315446165293)
        ·
          refine ⟨34340192322772618292311985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91573846194060315446165293 34340192322772618292311985)
          ·
            refine ⟨25755144242079463719233989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34340192322772618292311985 25755144242079463719233989)
            ·
              refine ⟨4829089545389899447356373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25755144242079463719233989 4829089545389899447356373)
              ·
                refine ⟨113181786220075768297415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4829089545389899447356373 113181786220075768297415)
                ·
                  rfl

theorem cell22_2975680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 7].length) (baseStart_2975680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975680 prefixEnd_2975680 := by exact prefixLift 2975680
  have htrace : WordTrace (prefixWord ++ tailWord_2975680) baseStart_2975680 baseEnd_2975680 := by
    simpa [prefixWord, tailWord_2975680, baseEnd_2975680] using wordTrace_append hprefix tailTrace_2975680
  have hstable : (prefixWord ++ tailWord_2975680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975680).length < 2 ^ (prefixWord ++ tailWord_2975680).sum := by decide
  have hdescent : baseEnd_2975680 < baseStart_2975680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975714 : List Nat := [3, 3, 3, 1, 3, 9]
def baseStart_2975714 : Nat := 118140960795 + 2975714 * 2 ^ 59
def prefixEnd_2975714 : Nat := 4983230072969 + 3 ^ 40 * 2975714 * 2
def baseEnd_2975714 : Nat := 12575897714512557522551

theorem tailTrace_2975714 : CollatzResearch.WordTrace tailWord_2975714 prefixEnd_2975714 12575897714512557522551 := by
  unfold tailWord_2975714
  simp only [CollatzResearch.WordTrace]
  refine ⟨27133301485375966083881549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72355470627669242890350797 27133301485375966083881549)
  ·
    refine ⟨10174988057015987281455581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27133301485375966083881549 10174988057015987281455581)
    ·
      refine ⟨3815620521380995230545843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10174988057015987281455581 3815620521380995230545843)
      ·
        refine ⟨5723430782071492845818765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3815620521380995230545843 5723430782071492845818765)
        ·
          refine ⟨2146286543276809817182037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5723430782071492845818765 2146286543276809817182037)
          ·
            refine ⟨12575897714512557522551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2146286543276809817182037 12575897714512557522551)
            ·
              rfl

theorem cell22_2975714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 9].length) (baseStart_2975714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975714 prefixEnd_2975714 := by exact prefixLift 2975714
  have htrace : WordTrace (prefixWord ++ tailWord_2975714) baseStart_2975714 baseEnd_2975714 := by
    simpa [prefixWord, tailWord_2975714, baseEnd_2975714] using wordTrace_append hprefix tailTrace_2975714
  have hstable : (prefixWord ++ tailWord_2975714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975714).length < 2 ^ (prefixWord ++ tailWord_2975714).sum := by decide
  have hdescent : baseEnd_2975714 < baseStart_2975714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975817 : List Nat := [1, 2, 1, 1, 2, 2, 4, 3, 2, 4]
def baseStart_2975817 : Nat := 118140960795 + 2975817 * 2 ^ 59
def prefixEnd_2975817 : Nat := 4983230072969 + 3 ^ 40 * 2975817 * 2
def baseEnd_2975817 : Nat := 1018682973880459224001315

theorem tailTrace_2975817 : CollatzResearch.WordTrace tailWord_2975817 prefixEnd_2975817 1018682973880459224001315 := by
  unfold tailWord_2975817
  simp only [CollatzResearch.WordTrace]
  refine ⟨108536962660130712926525705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72357975106753808617683803 108536962660130712926525705)
  ·
    refine ⟨81402721995098034694894279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108536962660130712926525705 81402721995098034694894279)
    ·
      refine ⟨122104082992647052042341419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81402721995098034694894279 122104082992647052042341419)
      ·
        refine ⟨183156124488970578063512129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122104082992647052042341419 183156124488970578063512129)
        ·
          refine ⟨137367093366727933547634097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183156124488970578063512129 137367093366727933547634097)
          ·
            refine ⟨103025320025045950160725573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137367093366727933547634097 103025320025045950160725573)
            ·
              refine ⟨19317247504696115655136045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103025320025045950160725573 19317247504696115655136045)
              ·
                refine ⟨7243967814261043370676017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19317247504696115655136045 7243967814261043370676017)
                ·
                  refine ⟨5432975860695782528007013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7243967814261043370676017 5432975860695782528007013)
                  ·
                    refine ⟨1018682973880459224001315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5432975860695782528007013 1018682973880459224001315)
                    ·
                      rfl

theorem cell22_2975817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_2975817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975817 prefixEnd_2975817 := by exact prefixLift 2975817
  have htrace : WordTrace (prefixWord ++ tailWord_2975817) baseStart_2975817 baseEnd_2975817 := by
    simpa [prefixWord, tailWord_2975817, baseEnd_2975817] using wordTrace_append hprefix tailTrace_2975817
  have hstable : (prefixWord ++ tailWord_2975817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975817).length < 2 ^ (prefixWord ++ tailWord_2975817).sum := by decide
  have hdescent : baseEnd_2975817 < baseStart_2975817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975832 : List Nat := [2, 1, 2, 2, 1, 6, 8]
def baseStart_2975832 : Nat := 118140960795 + 2975832 * 2 ^ 59
def prefixEnd_2975832 : Nat := 4983230072969 + 3 ^ 40 * 2975832 * 2
def baseEnd_2975832 : Nat := 37729189210629784625047

theorem tailTrace_2975832 : CollatzResearch.WordTrace tailWord_2975832 prefixEnd_2975832 37729189210629784625047 := by
  unfold tailWord_2975832
  simp only [CollatzResearch.WordTrace]
  refine ⟨54268754877538185244160875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72358339836717580325547833 54268754877538185244160875)
  ·
    refine ⟨81403132316307277866241313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54268754877538185244160875 81403132316307277866241313)
    ·
      refine ⟨61052349237230458399680985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81403132316307277866241313 61052349237230458399680985)
      ·
        refine ⟨45789261927922843799760739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61052349237230458399680985 45789261927922843799760739)
        ·
          refine ⟨68683892891884265699641109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45789261927922843799760739 68683892891884265699641109)
          ·
            refine ⟨3219557479307074954670677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68683892891884265699641109 3219557479307074954670677)
            ·
              refine ⟨37729189210629784625047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3219557479307074954670677 37729189210629784625047)
              ·
                rfl

theorem cell22_2975832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 8].length) (baseStart_2975832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975832 prefixEnd_2975832 := by exact prefixLift 2975832
  have htrace : WordTrace (prefixWord ++ tailWord_2975832) baseStart_2975832 baseEnd_2975832 := by
    simpa [prefixWord, tailWord_2975832, baseEnd_2975832] using wordTrace_append hprefix tailTrace_2975832
  have hstable : (prefixWord ++ tailWord_2975832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975832).length < 2 ^ (prefixWord ++ tailWord_2975832).sum := by decide
  have hdescent : baseEnd_2975832 < baseStart_2975832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975881 : List Nat := [1, 2, 1, 1, 4, 2, 2, 5, 1, 3]
def baseStart_2975881 : Nat := 118140960795 + 2975881 * 2 ^ 59
def prefixEnd_2975881 : Nat := 4983230072969 + 3 ^ 40 * 2975881 * 2
def baseEnd_2975881 : Nat := 1018704882388384390401119

theorem tailTrace_2975881 : CollatzResearch.WordTrace tailWord_2975881 prefixEnd_2975881 1018704882388384390401119 := by
  unfold tailWord_2975881
  simp only [CollatzResearch.WordTrace]
  refine ⟨108539296931898851856855497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72359531287932567904570331 108539296931898851856855497)
  ·
    refine ⟨81404472698924138892641623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108539296931898851856855497 81404472698924138892641623)
    ·
      refine ⟨122106709048386208338962435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81404472698924138892641623 122106709048386208338962435)
      ·
        refine ⟨183160063572579312508443653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122106709048386208338962435 183160063572579312508443653)
        ·
          refine ⟨34342511919858621095333185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183160063572579312508443653 34342511919858621095333185)
          ·
            refine ⟨25756883939893965821499889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34342511919858621095333185 25756883939893965821499889)
            ·
              refine ⟨19317662954920474366124917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25756883939893965821499889 19317662954920474366124917)
              ·
                refine ⟨1811030902023794471824211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19317662954920474366124917 1811030902023794471824211)
                ·
                  refine ⟨2716546353035691707736317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811030902023794471824211 2716546353035691707736317)
                  ·
                    refine ⟨1018704882388384390401119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2716546353035691707736317 1018704882388384390401119)
                    ·
                      rfl

theorem cell22_2975881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 1, 3].length) (baseStart_2975881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975881 prefixEnd_2975881 := by exact prefixLift 2975881
  have htrace : WordTrace (prefixWord ++ tailWord_2975881) baseStart_2975881 baseEnd_2975881 := by
    simpa [prefixWord, tailWord_2975881, baseEnd_2975881] using wordTrace_append hprefix tailTrace_2975881
  have hstable : (prefixWord ++ tailWord_2975881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975881).length < 2 ^ (prefixWord ++ tailWord_2975881).sum := by decide
  have hdescent : baseEnd_2975881 < baseStart_2975881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975941 : List Nat := [1, 3, 1, 1, 1, 1, 8, 1, 1, 4]
def baseStart_2975941 : Nat := 118140960795 + 2975941 * 2 ^ 59
def prefixEnd_2975941 : Nat := 4983230072969 + 3 ^ 40 * 2975941 * 2
def baseEnd_2975941 : Nat := 1018725421614564233900935

theorem tailTrace_2975941 : CollatzResearch.WordTrace tailWord_2975941 prefixEnd_2975941 1018725421614564233900935 := by
  unfold tailWord_2975941
  simp only [CollatzResearch.WordTrace]
  refine ⟨108541485311681482104039677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72360990207787654736026451 108541485311681482104039677)
  ·
    refine ⟨40703056991880555789014879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108541485311681482104039677 40703056991880555789014879)
    ·
      refine ⟨61054585487820833683522319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40703056991880555789014879 61054585487820833683522319)
      ·
        refine ⟨91581878231731250525283479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61054585487820833683522319 91581878231731250525283479)
        ·
          refine ⟨137372817347596875787925219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91581878231731250525283479 137372817347596875787925219)
          ·
            refine ⟨206059226021395313681887829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137372817347596875787925219 206059226021395313681887829)
            ·
              refine ⟨2414756554938226332209623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 206059226021395313681887829 2414756554938226332209623)
              ·
                refine ⟨3622134832407339498314435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2414756554938226332209623 3622134832407339498314435)
                ·
                  refine ⟨5433202248611009247471653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3622134832407339498314435 5433202248611009247471653)
                  ·
                    refine ⟨1018725421614564233900935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5433202248611009247471653 1018725421614564233900935)
                    ·
                      rfl

theorem cell22_2975941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 1, 4].length) (baseStart_2975941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975941 prefixEnd_2975941 := by exact prefixLift 2975941
  have htrace : WordTrace (prefixWord ++ tailWord_2975941) baseStart_2975941 baseEnd_2975941 := by
    simpa [prefixWord, tailWord_2975941, baseEnd_2975941] using wordTrace_append hprefix tailTrace_2975941
  have hstable : (prefixWord ++ tailWord_2975941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975941).length < 2 ^ (prefixWord ++ tailWord_2975941).sum := by decide
  have hdescent : baseEnd_2975941 < baseStart_2975941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975967 : List Nat := [1, 1, 2, 3, 2, 1, 1, 11]
def baseStart_2975967 : Nat := 118140960795 + 2975967 * 2 ^ 59
def prefixEnd_2975967 : Nat := 4983230072969 + 3 ^ 40 * 2975967 * 2
def baseEnd_2975967 : Nat := 113192702438434314750095

theorem tailTrace_2975967 : CollatzResearch.WordTrace tailWord_2975967 prefixEnd_2975967 113192702438434314750095 := by
  unfold tailWord_2975967
  simp only [CollatzResearch.WordTrace]
  refine ⟨108542433609587288544486155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72361622406391525696324103 108542433609587288544486155)
  ·
    refine ⟨162813650414380932816729233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108542433609587288544486155 162813650414380932816729233)
    ·
      refine ⟨122110237810785699612546925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162813650414380932816729233 122110237810785699612546925)
      ·
        refine ⟨45791339179044637354705097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122110237810785699612546925 45791339179044637354705097)
        ·
          refine ⟨34343504384283478016028823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45791339179044637354705097 34343504384283478016028823)
          ·
            refine ⟨51515256576425217024043235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34343504384283478016028823 51515256576425217024043235)
            ·
              refine ⟨77272884864637825536064853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51515256576425217024043235 77272884864637825536064853)
              ·
                refine ⟨113192702438434314750095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 77272884864637825536064853 113192702438434314750095)
                ·
                  rfl

theorem cell22_2975967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 11].length) (baseStart_2975967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2975967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2975967 prefixEnd_2975967 := by exact prefixLift 2975967
  have htrace : WordTrace (prefixWord ++ tailWord_2975967) baseStart_2975967 baseEnd_2975967 := by
    simpa [prefixWord, tailWord_2975967, baseEnd_2975967] using wordTrace_append hprefix tailTrace_2975967
  have hstable : (prefixWord ++ tailWord_2975967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975967).length < 2 ^ (prefixWord ++ tailWord_2975967).sum := by decide
  have hdescent : baseEnd_2975967 < baseStart_2975967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976014 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_2976014 : Nat := 118140960795 + 2976014 * 2 ^ 59
def prefixEnd_2976014 : Nat := 4983230072969 + 3 ^ 40 * 2976014 * 2
def baseEnd_2976014 : Nat := 1018750411006416376825711

theorem tailTrace_2976014 : CollatzResearch.WordTrace tailWord_2976014 prefixEnd_2976014 1018750411006416376825711 := by
  unfold tailWord_2976014
  simp only [CollatzResearch.WordTrace]
  refine ⟨13568018480052126946430887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72362765226944677047631397 13568018480052126946430887)
  ·
    refine ⟨20352027720078190419646331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13568018480052126946430887 20352027720078190419646331)
    ·
      refine ⟨30528041580117285629469497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20352027720078190419646331 30528041580117285629469497)
      ·
        refine ⟨22896031185087964222102123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30528041580117285629469497 22896031185087964222102123)
        ·
          refine ⟨34344046777631946333153185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22896031185087964222102123 34344046777631946333153185)
          ·
            refine ⟨25758035083223959749864889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34344046777631946333153185 25758035083223959749864889)
            ·
              refine ⟨19318526312417969812398667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25758035083223959749864889 19318526312417969812398667)
              ·
                refine ⟨28977789468626954718598001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19318526312417969812398667 28977789468626954718598001)
                ·
                  refine ⟨21733342101470216038948501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28977789468626954718598001 21733342101470216038948501)
                  ·
                    refine ⟨1018750411006416376825711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21733342101470216038948501 1018750411006416376825711)
                    ·
                      rfl

theorem cell22_2976014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_2976014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976014 prefixEnd_2976014 := by exact prefixLift 2976014
  have htrace : WordTrace (prefixWord ++ tailWord_2976014) baseStart_2976014 baseEnd_2976014 := by
    simpa [prefixWord, tailWord_2976014, baseEnd_2976014] using wordTrace_append hprefix tailTrace_2976014
  have hstable : (prefixWord ++ tailWord_2976014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976014).length < 2 ^ (prefixWord ++ tailWord_2976014).sum := by decide
  have hdescent : baseEnd_2976014 < baseStart_2976014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976123 : List Nat := [1, 1, 1, 1, 1, 7, 3, 2, 2, 3]
def baseStart_2976123 : Nat := 118140960795 + 2976123 * 2 ^ 59
def prefixEnd_2976123 : Nat := 4983230072969 + 3 ^ 40 * 2976123 * 2
def baseEnd_2976123 : Nat := 1018787723933976425850377

theorem tailTrace_2976123 : CollatzResearch.WordTrace tailWord_2976123 prefixEnd_2976123 1018787723933976425850377 := by
  unfold tailWord_2976123
  simp only [CollatzResearch.WordTrace]
  refine ⟨108548123397022127187165023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72365415598014751458110015 108548123397022127187165023)
  ·
    refine ⟨162822185095533190780747535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108548123397022127187165023 162822185095533190780747535)
    ·
      refine ⟨244233277643299786171121303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162822185095533190780747535 244233277643299786171121303)
      ·
        refine ⟨366349916464949679256681955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244233277643299786171121303 366349916464949679256681955)
        ·
          refine ⟨549524874697424518885022933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366349916464949679256681955 549524874697424518885022933)
          ·
            refine ⟨12879489250720887161367725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 549524874697424518885022933 12879489250720887161367725)
            ·
              refine ⟨4829808469020332685512897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12879489250720887161367725 4829808469020332685512897)
              ·
                refine ⟨3622356351765249514134673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4829808469020332685512897 3622356351765249514134673)
                ·
                  refine ⟨2716767263823937135601005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3622356351765249514134673 2716767263823937135601005)
                  ·
                    refine ⟨1018787723933976425850377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2716767263823937135601005 1018787723933976425850377)
                    ·
                      rfl

theorem cell22_2976123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 3].length) (baseStart_2976123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976123 prefixEnd_2976123 := by exact prefixLift 2976123
  have htrace : WordTrace (prefixWord ++ tailWord_2976123) baseStart_2976123 baseEnd_2976123 := by
    simpa [prefixWord, tailWord_2976123, baseEnd_2976123] using wordTrace_append hprefix tailTrace_2976123
  have hstable : (prefixWord ++ tailWord_2976123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976123).length < 2 ^ (prefixWord ++ tailWord_2976123).sum := by decide
  have hdescent : baseEnd_2976123 < baseStart_2976123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976140 : List Nat := [2, 2, 1, 2, 1, 5, 3, 1, 2, 3]
def baseStart_2976140 : Nat := 118140960795 + 2976140 * 2 ^ 59
def prefixEnd_2976140 : Nat := 4983230072969 + 3 ^ 40 * 2976140 * 2
def baseEnd_2976140 : Nat := 1018793543381394048175325

theorem tailTrace_2976140 : CollatzResearch.WordTrace tailWord_2976140 prefixEnd_2976140 1018793543381394048175325 := by
  unfold tailWord_2976140
  simp only [CollatzResearch.WordTrace]
  refine ⟨54274371718980269545266937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72365828958640359393689249 54274371718980269545266937)
  ·
    refine ⟨40705778789235202158950203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54274371718980269545266937 40705778789235202158950203)
    ·
      refine ⟨61058668183852803238425305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40705778789235202158950203 61058668183852803238425305)
      ·
        refine ⟨45794001137889602428818979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61058668183852803238425305 45794001137889602428818979)
        ·
          refine ⟨68691001706834403643228469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45794001137889602428818979 68691001706834403643228469)
          ·
            refine ⟨6439781410015725341552669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68691001706834403643228469 6439781410015725341552669)
            ·
              refine ⟨2414918028755897003082251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6439781410015725341552669 2414918028755897003082251)
              ·
                refine ⟨3622377043133845504623377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2414918028755897003082251 3622377043133845504623377)
                ·
                  refine ⟨2716782782350384128467533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3622377043133845504623377 2716782782350384128467533)
                  ·
                    refine ⟨1018793543381394048175325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2716782782350384128467533 1018793543381394048175325)
                    ·
                      rfl

theorem cell22_2976140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 2, 3].length) (baseStart_2976140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976140 prefixEnd_2976140 := by exact prefixLift 2976140
  have htrace : WordTrace (prefixWord ++ tailWord_2976140) baseStart_2976140 baseEnd_2976140 := by
    simpa [prefixWord, tailWord_2976140, baseEnd_2976140] using wordTrace_append hprefix tailTrace_2976140
  have hstable : (prefixWord ++ tailWord_2976140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976140).length < 2 ^ (prefixWord ++ tailWord_2976140).sum := by decide
  have hdescent : baseEnd_2976140 < baseStart_2976140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976185 : List Nat := [1, 2, 1, 4, 3, 3, 1, 1, 3, 3]
def baseStart_2976185 : Nat := 118140960795 + 2976185 * 2 ^ 59
def prefixEnd_2976185 : Nat := 4983230072969 + 3 ^ 40 * 2976185 * 2
def baseEnd_2976185 : Nat := 1018808947801028930800187

theorem tailTrace_2976185 : CollatzResearch.WordTrace tailWord_2976185 prefixEnd_2976185 1018808947801028930800187 := by
  unfold tailWord_2976185
  simp only [CollatzResearch.WordTrace]
  refine ⟨108550384722797511775922009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72366923148531674517281339 108550384722797511775922009)
  ·
    refine ⟨81412788542098133831941507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108550384722797511775922009 81412788542098133831941507)
    ·
      refine ⟨122119182813147200747912261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81412788542098133831941507 122119182813147200747912261)
      ·
        refine ⟨22897346777465100140233549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122119182813147200747912261 22897346777465100140233549)
        ·
          refine ⟨8586505041549412552587581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22897346777465100140233549 8586505041549412552587581)
          ·
            refine ⟨3219939390581029707220343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8586505041549412552587581 3219939390581029707220343)
            ·
              refine ⟨4829909085871544560830515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3219939390581029707220343 4829909085871544560830515)
              ·
                refine ⟨7244863628807316841245773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4829909085871544560830515 7244863628807316841245773)
                ·
                  refine ⟨2716823860802743815467165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7244863628807316841245773 2716823860802743815467165)
                  ·
                    refine ⟨1018808947801028930800187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2716823860802743815467165 1018808947801028930800187)
                    ·
                      rfl

theorem cell22_2976185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 3].length) (baseStart_2976185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976185 prefixEnd_2976185 := by exact prefixLift 2976185
  have htrace : WordTrace (prefixWord ++ tailWord_2976185) baseStart_2976185 baseEnd_2976185 := by
    simpa [prefixWord, tailWord_2976185, baseEnd_2976185] using wordTrace_append hprefix tailTrace_2976185
  have hstable : (prefixWord ++ tailWord_2976185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976185).length < 2 ^ (prefixWord ++ tailWord_2976185).sum := by decide
  have hdescent : baseEnd_2976185 < baseStart_2976185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976241 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 3, 5]
def baseStart_2976241 : Nat := 118140960795 + 2976241 * 2 ^ 59
def prefixEnd_2976241 : Nat := 4983230072969 + 3 ^ 40 * 2976241 * 2
def baseEnd_2976241 : Nat := 1018828117745463451400015

theorem tailTrace_2976241 : CollatzResearch.WordTrace tailWord_2976241 prefixEnd_2976241 1018828117745463451400015 := by
  unfold tailWord_2976241
  simp only [CollatzResearch.WordTrace]
  refine ⟨108552427210594633339960577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72368284807063088893307051 108552427210594633339960577)
  ·
    refine ⟨81414320407945975004970433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108552427210594633339960577 81414320407945975004970433)
    ·
      refine ⟨61060740305959481253727825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81414320407945975004970433 61060740305959481253727825)
      ·
        refine ⟨45795555229469610940295869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61060740305959481253727825 45795555229469610940295869)
        ·
          refine ⟨17173333211051104102610951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45795555229469610940295869 17173333211051104102610951)
          ·
            refine ⟨25759999816576656153916427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17173333211051104102610951 25759999816576656153916427)
            ·
              refine ⟨38639999724864984230874641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25759999816576656153916427 38639999724864984230874641)
              ·
                refine ⟨28979999793648738173155981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38639999724864984230874641 28979999793648738173155981)
                ·
                  refine ⟨10867499922618276814933493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28979999793648738173155981 10867499922618276814933493)
                  ·
                    refine ⟨1018828117745463451400015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10867499922618276814933493 1018828117745463451400015)
                    ·
                      rfl

theorem cell22_2976241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_2976241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976241 prefixEnd_2976241 := by exact prefixLift 2976241
  have htrace : WordTrace (prefixWord ++ tailWord_2976241) baseStart_2976241 baseEnd_2976241 := by
    simpa [prefixWord, tailWord_2976241, baseEnd_2976241] using wordTrace_append hprefix tailTrace_2976241
  have hstable : (prefixWord ++ tailWord_2976241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976241).length < 2 ^ (prefixWord ++ tailWord_2976241).sum := by decide
  have hdescent : baseEnd_2976241 < baseStart_2976241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976243 : List Nat := [1, 1, 1, 2, 2, 2, 5, 4, 4]
def baseStart_2976243 : Nat := 118140960795 + 2976243 * 2 ^ 59
def prefixEnd_2976243 : Nat := 4983230072969 + 3 ^ 40 * 2976243 * 2
def baseEnd_2976243 : Nat := 339609600795445370950003

theorem tailTrace_2976243 : CollatzResearch.WordTrace tailWord_2976243 prefixEnd_2976243 339609600795445370950003 := by
  unfold tailWord_2976243
  simp only [CollatzResearch.WordTrace]
  refine ⟨108552500156587387681533383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72368333437724925121022255 108552500156587387681533383)
  ·
    refine ⟨162828750234881081522300075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108552500156587387681533383 162828750234881081522300075)
    ·
      refine ⟨244243125352321622283450113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162828750234881081522300075 244243125352321622283450113)
      ·
        refine ⟨183182344014241216712587585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244243125352321622283450113 183182344014241216712587585)
        ·
          refine ⟨137386758010680912534440689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183182344014241216712587585 137386758010680912534440689)
          ·
            refine ⟨103040068508010684400830517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137386758010680912534440689 103040068508010684400830517)
            ·
              refine ⟨9660006422626001662577861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103040068508010684400830517 9660006422626001662577861)
              ·
                refine ⟨1811251204242375311733349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9660006422626001662577861 1811251204242375311733349)
                ·
                  refine ⟨339609600795445370950003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1811251204242375311733349 339609600795445370950003)
                  ·
                    rfl

theorem cell22_2976243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 4].length) (baseStart_2976243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976243 prefixEnd_2976243 := by exact prefixLift 2976243
  have htrace : WordTrace (prefixWord ++ tailWord_2976243) baseStart_2976243 baseEnd_2976243 := by
    simpa [prefixWord, tailWord_2976243, baseEnd_2976243] using wordTrace_append hprefix tailTrace_2976243
  have hstable : (prefixWord ++ tailWord_2976243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976243).length < 2 ^ (prefixWord ++ tailWord_2976243).sum := by decide
  have hdescent : baseEnd_2976243 < baseStart_2976243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976279 : List Nat := [1, 1, 3, 6, 1, 2, 2, 1, 1, 4]
def baseStart_2976279 : Nat := 118140960795 + 2976279 * 2 ^ 59
def prefixEnd_2976279 : Nat := 4983230072969 + 3 ^ 40 * 2976279 * 2
def baseEnd_2976279 : Nat := 1018841125922044018949899

theorem tailTrace_2976279 : CollatzResearch.WordTrace tailWord_2976279 prefixEnd_2976279 1018841125922044018949899 := by
  unfold tailWord_2976279
  simp only [CollatzResearch.WordTrace]
  refine ⟨108553813184456965829843891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72369208789637977219895927 108553813184456965829843891)
  ·
    refine ⟨162830719776685448744765837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108553813184456965829843891 162830719776685448744765837)
    ·
      refine ⟨61061519916257043279287189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162830719776685448744765837 61061519916257043279287189)
      ·
        refine ⟨2862258746074548903716587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61061519916257043279287189 2862258746074548903716587)
        ·
          refine ⟨4293388119111823355574881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2862258746074548903716587 4293388119111823355574881)
          ·
            refine ⟨3220041089333867516681161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4293388119111823355574881 3220041089333867516681161)
            ·
              refine ⟨2415030817000400637510871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3220041089333867516681161 2415030817000400637510871)
              ·
                refine ⟨3622546225500600956266307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2415030817000400637510871 3622546225500600956266307)
                ·
                  refine ⟨5433819338250901434399461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3622546225500600956266307 5433819338250901434399461)
                  ·
                    refine ⟨1018841125922044018949899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5433819338250901434399461 1018841125922044018949899)
                    ·
                      rfl

theorem cell22_2976279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 1, 4].length) (baseStart_2976279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976279 prefixEnd_2976279 := by exact prefixLift 2976279
  have htrace : WordTrace (prefixWord ++ tailWord_2976279) baseStart_2976279 baseEnd_2976279 := by
    simpa [prefixWord, tailWord_2976279, baseEnd_2976279] using wordTrace_append hprefix tailTrace_2976279
  have hstable : (prefixWord ++ tailWord_2976279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976279).length < 2 ^ (prefixWord ++ tailWord_2976279).sum := by decide
  have hdescent : baseEnd_2976279 < baseStart_2976279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976288 : List Nat := [2, 1, 1, 6, 2, 1, 9]
def baseStart_2976288 : Nat := 118140960795 + 2976288 * 2 ^ 59
def prefixEnd_2976288 : Nat := 4983230072969 + 3 ^ 40 * 2976288 * 2
def baseEnd_2976288 : Nat := 37734970622443370202773

theorem tailTrace_2976288 : CollatzResearch.WordTrace tailWord_2976288 prefixEnd_2976288 37734970622443370202773 := by
  unfold tailWord_2976288
  simp only [CollatzResearch.WordTrace]
  refine ⟨54277070720712180183460759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72369427627616240244614345 54277070720712180183460759)
  ·
    refine ⟨81415606081068270275191139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54277070720712180183460759 81415606081068270275191139)
    ·
      refine ⟨122123409121602405412786709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81415606081068270275191139 122123409121602405412786709)
      ·
        refine ⟨5724534802575112753724377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122123409121602405412786709 5724534802575112753724377)
        ·
          refine ⟨4293401101931334565293283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5724534802575112753724377 4293401101931334565293283)
          ·
            refine ⟨6440101652897001847939925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4293401101931334565293283 6440101652897001847939925)
            ·
              refine ⟨37734970622443370202773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6440101652897001847939925 37734970622443370202773)
              ·
                rfl

theorem cell22_2976288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 9].length) (baseStart_2976288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976288 prefixEnd_2976288 := by exact prefixLift 2976288
  have htrace : WordTrace (prefixWord ++ tailWord_2976288) baseStart_2976288 baseEnd_2976288 := by
    simpa [prefixWord, tailWord_2976288, baseEnd_2976288] using wordTrace_append hprefix tailTrace_2976288
  have hstable : (prefixWord ++ tailWord_2976288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976288).length < 2 ^ (prefixWord ++ tailWord_2976288).sum := by decide
  have hdescent : baseEnd_2976288 < baseStart_2976288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976292 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 4, 3]
def baseStart_2976292 : Nat := 118140960795 + 2976292 * 2 ^ 59
def prefixEnd_2976292 : Nat := 4983230072969 + 3 ^ 40 * 2976292 * 2
def baseEnd_2976292 : Nat := 1018845576087716318374859

theorem tailTrace_2976292 : CollatzResearch.WordTrace tailWord_2976292 prefixEnd_2976292 1018845576087716318374859 := by
  unfold tailWord_2976292
  simp only [CollatzResearch.WordTrace]
  refine ⟨54277143666704934525033565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72369524888939912700044753 54277143666704934525033565)
  ·
    refine ⟨20353928875014350446887587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54277143666704934525033565 20353928875014350446887587)
    ·
      refine ⟨30530893312521525670331381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20353928875014350446887587 30530893312521525670331381)
      ·
        refine ⟨2862271248048893031593567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30530893312521525670331381 2862271248048893031593567)
        ·
          refine ⟨4293406872073339547390351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2862271248048893031593567 4293406872073339547390351)
          ·
            refine ⟨6440110308110009321085527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4293406872073339547390351 6440110308110009321085527)
            ·
              refine ⟨9660165462165013981628291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6440110308110009321085527 9660165462165013981628291)
              ·
                refine ⟨14490248193247520972442437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9660165462165013981628291 14490248193247520972442437)
                ·
                  refine ⟨2716921536233910182332957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14490248193247520972442437 2716921536233910182332957)
                  ·
                    refine ⟨1018845576087716318374859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2716921536233910182332957 1018845576087716318374859)
                    ·
                      rfl

theorem cell22_2976292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_2976292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976292 prefixEnd_2976292 := by exact prefixLift 2976292
  have htrace : WordTrace (prefixWord ++ tailWord_2976292) baseStart_2976292 baseEnd_2976292 := by
    simpa [prefixWord, tailWord_2976292, baseEnd_2976292] using wordTrace_append hprefix tailTrace_2976292
  have hstable : (prefixWord ++ tailWord_2976292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976292).length < 2 ^ (prefixWord ++ tailWord_2976292).sum := by decide
  have hdescent : baseEnd_2976292 < baseStart_2976292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976331 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 1, 7]
def baseStart_2976331 : Nat := 118140960795 + 2976331 * 2 ^ 59
def prefixEnd_2976331 : Nat := 4983230072969 + 3 ^ 40 * 2976331 * 2
def baseEnd_2976331 : Nat := 1018858926584733216649739

theorem tailTrace_2976331 : CollatzResearch.WordTrace tailWord_2976331 prefixEnd_2976331 1018858926584733216649739 := by
  unfold tailWord_2976331
  simp only [CollatzResearch.WordTrace]
  refine ⟨108555709780268578710736847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72370473186845719140491231 108555709780268578710736847)
  ·
    refine ⟨162833564670402868066105271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108555709780268578710736847 162833564670402868066105271)
    ·
      refine ⟨244250347005604302099157907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162833564670402868066105271 244250347005604302099157907)
      ·
        refine ⟨366375520508406453148736861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244250347005604302099157907 366375520508406453148736861)
        ·
          refine ⟨137390820190652419930776323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 366375520508406453148736861 137390820190652419930776323)
          ·
            refine ⟨206086230285978629896164485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137390820190652419930776323 206086230285978629896164485)
            ·
              refine ⟨38641168178620993105530841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206086230285978629896164485 38641168178620993105530841)
              ·
                refine ⟨28980876133965744829148131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38641168178620993105530841 28980876133965744829148131)
                ·
                  refine ⟨43471314200948617243722197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28980876133965744829148131 43471314200948617243722197)
                  ·
                    refine ⟨1018858926584733216649739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43471314200948617243722197 1018858926584733216649739)
                    ·
                      rfl

theorem cell22_2976331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 7].length) (baseStart_2976331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976331 prefixEnd_2976331 := by exact prefixLift 2976331
  have htrace : WordTrace (prefixWord ++ tailWord_2976331) baseStart_2976331 baseEnd_2976331 := by
    simpa [prefixWord, tailWord_2976331, baseEnd_2976331] using wordTrace_append hprefix tailTrace_2976331
  have hstable : (prefixWord ++ tailWord_2976331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976331).length < 2 ^ (prefixWord ++ tailWord_2976331).sum := by decide
  have hdescent : baseEnd_2976331 < baseStart_2976331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976337 : List Nat := [1, 2, 2, 1, 3, 3, 3, 3, 1, 3]
def baseStart_2976337 : Nat := 118140960795 + 2976337 * 2 ^ 59
def prefixEnd_2976337 : Nat := 4983230072969 + 3 ^ 40 * 2976337 * 2
def baseEnd_2976337 : Nat := 1018860980507351200999721

theorem tailTrace_2976337 : CollatzResearch.WordTrace tailWord_2976337 prefixEnd_2976337 1018860980507351200999721 := by
  unfold tailWord_2976337
  simp only [CollatzResearch.WordTrace]
  refine ⟨108555928618246841735455265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72370619078831227823636843 108555928618246841735455265)
  ·
    refine ⟨81416946463685131301591449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108555928618246841735455265 81416946463685131301591449)
    ·
      refine ⟨61062709847763848476193587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81416946463685131301591449 61062709847763848476193587)
      ·
        refine ⟨91594064771645772714290381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61062709847763848476193587 91594064771645772714290381)
        ·
          refine ⟨34347774289367164767858893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91594064771645772714290381 34347774289367164767858893)
          ·
            refine ⟨12880415358512686787947085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34347774289367164767858893 12880415358512686787947085)
            ·
              refine ⟨4830155759442257545480157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12880415358512686787947085 4830155759442257545480157)
              ·
                refine ⟨1811308409790846579555059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4830155759442257545480157 1811308409790846579555059)
                ·
                  refine ⟨2716962614686269869332589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811308409790846579555059 2716962614686269869332589)
                  ·
                    refine ⟨1018860980507351200999721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2716962614686269869332589 1018860980507351200999721)
                    ·
                      rfl

theorem cell22_2976337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 1, 3].length) (baseStart_2976337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976337 prefixEnd_2976337 := by exact prefixLift 2976337
  have htrace : WordTrace (prefixWord ++ tailWord_2976337) baseStart_2976337 baseEnd_2976337 := by
    simpa [prefixWord, tailWord_2976337, baseEnd_2976337] using wordTrace_append hprefix tailTrace_2976337
  have hstable : (prefixWord ++ tailWord_2976337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976337).length < 2 ^ (prefixWord ++ tailWord_2976337).sum := by decide
  have hdescent : baseEnd_2976337 < baseStart_2976337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976380 : List Nat := [2, 2, 2, 1, 1, 2, 5, 2, 1, 4]
def baseStart_2976380 : Nat := 118140960795 + 2976380 * 2 ^ 59
def prefixEnd_2976380 : Nat := 4983230072969 + 3 ^ 40 * 2976380 * 2
def baseEnd_2976380 : Nat := 1018875700286113422174589

theorem tailTrace_2976380 : CollatzResearch.WordTrace tailWord_2976380 prefixEnd_2976380 1018875700286113422174589 := by
  unfold tailWord_2976380
  simp only [CollatzResearch.WordTrace]
  refine ⟨54278748478545530039635297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72371664638060706719513729 54278748478545530039635297)
  ·
    refine ⟨40709061358909147529726473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54278748478545530039635297 40709061358909147529726473)
    ·
      refine ⟨30531796019181860647294855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40709061358909147529726473 30531796019181860647294855)
      ·
        refine ⟨45797694028772790970942283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30531796019181860647294855 45797694028772790970942283)
        ·
          refine ⟨68696541043159186456413425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45797694028772790970942283 68696541043159186456413425)
          ·
            refine ⟨51522405782369389842310069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68696541043159186456413425 51522405782369389842310069)
            ·
              refine ⟨4830225542097130297716569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51522405782369389842310069 4830225542097130297716569)
              ·
                refine ⟨3622669156572847723287427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4830225542097130297716569 3622669156572847723287427)
                ·
                  refine ⟨5434003734859271584931141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3622669156572847723287427 5434003734859271584931141)
                  ·
                    refine ⟨1018875700286113422174589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5434003734859271584931141 1018875700286113422174589)
                    ·
                      rfl

theorem cell22_2976380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_2976380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976380 prefixEnd_2976380 := by exact prefixLift 2976380
  have htrace : WordTrace (prefixWord ++ tailWord_2976380) baseStart_2976380 baseEnd_2976380 := by
    simpa [prefixWord, tailWord_2976380, baseEnd_2976380] using wordTrace_append hprefix tailTrace_2976380
  have hstable : (prefixWord ++ tailWord_2976380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976380).length < 2 ^ (prefixWord ++ tailWord_2976380).sum := by decide
  have hdescent : baseEnd_2976380 < baseStart_2976380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976412 : List Nat := [2, 2, 3, 2, 2, 2, 1, 4, 4]
def baseStart_2976412 : Nat := 118140960795 + 2976412 * 2 ^ 59
def prefixEnd_2976412 : Nat := 4983230072969 + 3 ^ 40 * 2976412 * 2
def baseEnd_2976412 : Nat := 339628884846692001791497

theorem tailTrace_2976412 : CollatzResearch.WordTrace tailWord_2976412 prefixEnd_2976412 339628884846692001791497 := by
  unfold tailWord_2976412
  simp only [CollatzResearch.WordTrace]
  refine ⟨54279332046487564772217745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72372442728650086362956993 54279332046487564772217745)
  ·
    refine ⟨40709499034865673579163309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54279332046487564772217745 40709499034865673579163309)
    ·
      refine ⟨15266062138074627592186241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40709499034865673579163309 15266062138074627592186241)
      ·
        refine ⟨11449546603555970694139681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15266062138074627592186241 11449546603555970694139681)
        ·
          refine ⟨8587159952666978020604761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11449546603555970694139681 8587159952666978020604761)
          ·
            refine ⟨6440369964500233515453571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8587159952666978020604761 6440369964500233515453571)
            ·
              refine ⟨9660554946750350273180357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6440369964500233515453571 9660554946750350273180357)
              ·
                refine ⟨1811354052515690676221317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9660554946750350273180357 1811354052515690676221317)
                ·
                  refine ⟨339628884846692001791497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1811354052515690676221317 339628884846692001791497)
                  ·
                    rfl

theorem cell22_2976412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_2976412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976412 prefixEnd_2976412 := by exact prefixLift 2976412
  have htrace : WordTrace (prefixWord ++ tailWord_2976412) baseStart_2976412 baseEnd_2976412 := by
    simpa [prefixWord, tailWord_2976412, baseEnd_2976412] using wordTrace_append hprefix tailTrace_2976412
  have hstable : (prefixWord ++ tailWord_2976412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976412).length < 2 ^ (prefixWord ++ tailWord_2976412).sum := by decide
  have hdescent : baseEnd_2976412 < baseStart_2976412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976472 : List Nat := [2, 1, 2, 2, 3, 3, 2, 1, 3, 3]
def baseStart_2976472 : Nat := 118140960795 + 2976472 * 2 ^ 59
def prefixEnd_2976472 : Nat := 4983230072969 + 3 ^ 40 * 2976472 * 2
def baseEnd_2976472 : Nat := 1018907193766255848874307

theorem tailTrace_2976472 : CollatzResearch.WordTrace tailWord_2976472 prefixEnd_2976472 1018907193766255848874307 := by
  unfold tailWord_2976472
  simp only [CollatzResearch.WordTrace]
  refine ⟨54280426236378879895809835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72373901648505173194413113 54280426236378879895809835)
  ·
    refine ⟨81420639354568319843714753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54280426236378879895809835 81420639354568319843714753)
    ·
      refine ⟨61065479515926239882786065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81420639354568319843714753 61065479515926239882786065)
      ·
        refine ⟨45799109636944679912089549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61065479515926239882786065 45799109636944679912089549)
        ·
          refine ⟨17174666113854254967033581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45799109636944679912089549 17174666113854254967033581)
          ·
            refine ⟨6440499792695345612637593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17174666113854254967033581 6440499792695345612637593)
            ·
              refine ⟨4830374844521509209478195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6440499792695345612637593 4830374844521509209478195)
              ·
                refine ⟨7245562266782263814217293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4830374844521509209478195 7245562266782263814217293)
                ·
                  refine ⟨2717085850043348930331485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7245562266782263814217293 2717085850043348930331485)
                  ·
                    refine ⟨1018907193766255848874307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2717085850043348930331485 1018907193766255848874307)
                    ·
                      rfl

theorem cell22_2976472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_2976472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976472 prefixEnd_2976472 := by exact prefixLift 2976472
  have htrace : WordTrace (prefixWord ++ tailWord_2976472) baseStart_2976472 baseEnd_2976472 := by
    simpa [prefixWord, tailWord_2976472, baseEnd_2976472] using wordTrace_append hprefix tailTrace_2976472
  have hstable : (prefixWord ++ tailWord_2976472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976472).length < 2 ^ (prefixWord ++ tailWord_2976472).sum := by decide
  have hdescent : baseEnd_2976472 < baseStart_2976472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976545 : List Nat := [1, 2, 3, 2, 1, 2, 2, 3, 1, 5]
def baseStart_2976545 : Nat := 118140960795 + 2976545 * 2 ^ 59
def prefixEnd_2976545 : Nat := 4983230072969 + 3 ^ 40 * 2976545 * 2
def baseEnd_2976545 : Nat := 1018932183158107991799083

theorem tailTrace_2976545 : CollatzResearch.WordTrace tailWord_2976545 prefixEnd_2976545 1018932183158107991799083 := by
  unfold tailWord_2976545
  simp only [CollatzResearch.WordTrace]
  refine ⟨108563515001493293259027089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72375676667662195506018059 108563515001493293259027089)
  ·
    refine ⟨81422636251119969944270317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108563515001493293259027089 81422636251119969944270317)
    ·
      refine ⟨30533488594169988729101369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81422636251119969944270317 30533488594169988729101369)
      ·
        refine ⟨22900116445627491546826027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30533488594169988729101369 22900116445627491546826027)
        ·
          refine ⟨34350174668441237320239041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22900116445627491546826027 34350174668441237320239041)
          ·
            refine ⟨25762631001330927990179281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34350174668441237320239041 25762631001330927990179281)
            ·
              refine ⟨19321973250998195992634461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25762631001330927990179281 19321973250998195992634461)
              ·
                refine ⟨7245739969124323497237923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19321973250998195992634461 7245739969124323497237923)
                ·
                  refine ⟨10868609953686485245856885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7245739969124323497237923 10868609953686485245856885)
                  ·
                    refine ⟨1018932183158107991799083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10868609953686485245856885 1018932183158107991799083)
                    ·
                      rfl

theorem cell22_2976545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_2976545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976545 prefixEnd_2976545 := by exact prefixLift 2976545
  have htrace : WordTrace (prefixWord ++ tailWord_2976545) baseStart_2976545 baseEnd_2976545 := by
    simpa [prefixWord, tailWord_2976545, baseEnd_2976545] using wordTrace_append hprefix tailTrace_2976545
  have hstable : (prefixWord ++ tailWord_2976545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976545).length < 2 ^ (prefixWord ++ tailWord_2976545).sum := by decide
  have hdescent : baseEnd_2976545 < baseStart_2976545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976607 : List Nat := [1, 1, 2, 3, 1, 3, 3, 2, 3, 3]
def baseStart_2976607 : Nat := 118140960795 + 2976607 * 2 ^ 59
def prefixEnd_2976607 : Nat := 4983230072969 + 3 ^ 40 * 2976607 * 2
def baseEnd_2976607 : Nat := 1018953407025160496748893

theorem tailTrace_2976607 : CollatzResearch.WordTrace tailWord_2976607 prefixEnd_2976607 1018953407025160496748893 := by
  unfold tailWord_2976607
  simp only [CollatzResearch.WordTrace]
  refine ⟨108565776327268677847784075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72377184218179118565189383 108565776327268677847784075)
  ·
    refine ⟨162848664490903016771676113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108565776327268677847784075 162848664490903016771676113)
    ·
      refine ⟨122136498368177262578757085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162848664490903016771676113 122136498368177262578757085)
      ·
        refine ⟨45801186888066473467033907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122136498368177262578757085 45801186888066473467033907)
        ·
          refine ⟨68701780332099710200550861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45801186888066473467033907 68701780332099710200550861)
          ·
            refine ⟨25763167624537391325206573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68701780332099710200550861 25763167624537391325206573)
            ·
              refine ⟨9661187859201521746952465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25763167624537391325206573 9661187859201521746952465)
              ·
                refine ⟨7245890894401141310214349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9661187859201521746952465 7245890894401141310214349)
                ·
                  refine ⟨2717209085400427991330381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7245890894401141310214349 2717209085400427991330381)
                  ·
                    refine ⟨1018953407025160496748893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2717209085400427991330381 1018953407025160496748893)
                    ·
                      rfl

theorem cell22_2976607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 3].length) (baseStart_2976607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976607 prefixEnd_2976607 := by exact prefixLift 2976607
  have htrace : WordTrace (prefixWord ++ tailWord_2976607) baseStart_2976607 baseEnd_2976607 := by
    simpa [prefixWord, tailWord_2976607, baseEnd_2976607] using wordTrace_append hprefix tailTrace_2976607
  have hstable : (prefixWord ++ tailWord_2976607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976607).length < 2 ^ (prefixWord ++ tailWord_2976607).sum := by decide
  have hdescent : baseEnd_2976607 < baseStart_2976607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976620 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 7]
def baseStart_2976620 : Nat := 118140960795 + 2976620 * 2 ^ 59
def prefixEnd_2976620 : Nat := 4983230072969 + 3 ^ 40 * 2976620 * 2
def baseEnd_2976620 : Nat := 339652619063610932057951

theorem tailTrace_2976620 : CollatzResearch.WordTrace tailWord_2976620 prefixEnd_2976620 339652619063610932057951 := by
  unfold tailWord_2976620
  simp only [CollatzResearch.WordTrace]
  refine ⟨54283125238110790534003657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72377500317481054045338209 54283125238110790534003657)
  ·
    refine ⟨40712343928583092900502743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54283125238110790534003657 40712343928583092900502743)
    ·
      refine ⟨61068515892874639350754115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40712343928583092900502743 61068515892874639350754115)
      ·
        refine ⟨91602773839311959026131173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61068515892874639350754115 91602773839311959026131173)
        ·
          refine ⟨17175520094870992317399595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91602773839311959026131173 17175520094870992317399595)
          ·
            refine ⟨25763280142306488476099393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17175520094870992317399595 25763280142306488476099393)
            ·
              refine ⟨19322460106729866357074545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25763280142306488476099393 19322460106729866357074545)
              ·
                refine ⟨14491845080047399767805909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19322460106729866357074545 14491845080047399767805909)
                ·
                  refine ⟨339652619063610932057951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14491845080047399767805909 339652619063610932057951)
                  ·
                    rfl

theorem cell22_2976620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_2976620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976620 prefixEnd_2976620 := by exact prefixLift 2976620
  have htrace : WordTrace (prefixWord ++ tailWord_2976620) baseStart_2976620 baseEnd_2976620 := by
    simpa [prefixWord, tailWord_2976620, baseEnd_2976620] using wordTrace_append hprefix tailTrace_2976620
  have hstable : (prefixWord ++ tailWord_2976620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976620).length < 2 ^ (prefixWord ++ tailWord_2976620).sum := by decide
  have hdescent : baseEnd_2976620 < baseStart_2976620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976624 : List Nat := [2, 1, 1, 1, 4, 1, 3, 5, 1, 3]
def baseStart_2976624 : Nat := 118140960795 + 2976624 * 2 ^ 59
def prefixEnd_2976624 : Nat := 4983230072969 + 3 ^ 40 * 2976624 * 2
def baseEnd_2976624 : Nat := 1018959226472578119073841

theorem tailTrace_2976624 : CollatzResearch.WordTrace tailWord_2976624 prefixEnd_2976624 1018959226472578119073841 := by
  unfold tailWord_2976624
  simp only [CollatzResearch.WordTrace]
  refine ⟨54283198184103544875576463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72377597578804726500768617 54283198184103544875576463)
  ·
    refine ⟨81424797276155317313364695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54283198184103544875576463 81424797276155317313364695)
    ·
      refine ⟨122137195914232975970047043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81424797276155317313364695 122137195914232975970047043)
      ·
        refine ⟨183205793871349463955070565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122137195914232975970047043 183205793871349463955070565)
        ·
          refine ⟨34351086350878024491575731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183205793871349463955070565 34351086350878024491575731)
          ·
            refine ⟨51526629526317036737363597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34351086350878024491575731 51526629526317036737363597)
            ·
              refine ⟨19322486072368888776511349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51526629526317036737363597 19322486072368888776511349)
              ·
                refine ⟨1811483069284583322797939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19322486072368888776511349 1811483069284583322797939)
                ·
                  refine ⟨2717224603926874984196909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811483069284583322797939 2717224603926874984196909)
                  ·
                    refine ⟨1018959226472578119073841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2717224603926874984196909 1018959226472578119073841)
                    ·
                      rfl

theorem cell22_2976624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 1, 3].length) (baseStart_2976624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976624 prefixEnd_2976624 := by exact prefixLift 2976624
  have htrace : WordTrace (prefixWord ++ tailWord_2976624) baseStart_2976624 baseEnd_2976624 := by
    simpa [prefixWord, tailWord_2976624, baseEnd_2976624] using wordTrace_append hprefix tailTrace_2976624
  have hstable : (prefixWord ++ tailWord_2976624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976624).length < 2 ^ (prefixWord ++ tailWord_2976624).sum := by decide
  have hdescent : baseEnd_2976624 < baseStart_2976624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976635 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 2, 5]
def baseStart_2976635 : Nat := 118140960795 + 2976635 * 2 ^ 59
def prefixEnd_2976635 : Nat := 4983230072969 + 3 ^ 40 * 2976635 * 2
def baseEnd_2976635 : Nat := 1018962991997377757048807

theorem tailTrace_2976635 : CollatzResearch.WordTrace tailWord_2976635 prefixEnd_2976635 1018962991997377757048807 := by
  unfold tailWord_2976635
  simp only [CollatzResearch.WordTrace]
  refine ⟨108566797571167238629803359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72377865047444825753202239 108566797571167238629803359)
  ·
    refine ⟨162850196356750857944705039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108566797571167238629803359 162850196356750857944705039)
    ·
      refine ⟨244275294535126286917057559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162850196356750857944705039 244275294535126286917057559)
      ·
        refine ⟨366412941802689430375586339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244275294535126286917057559 366412941802689430375586339)
        ·
          refine ⟨549619412704034145563379509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366412941802689430375586339 549619412704034145563379509)
          ·
            refine ⟨51526819941003201146566829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 549619412704034145563379509 51526819941003201146566829)
            ·
              refine ⟨19322557477876200429962561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51526819941003201146566829 19322557477876200429962561)
              ·
                refine ⟨14491918108407150322471921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19322557477876200429962561 14491918108407150322471921)
                ·
                  refine ⟨10868938581305362741853941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14491918108407150322471921 10868938581305362741853941)
                  ·
                    refine ⟨1018962991997377757048807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10868938581305362741853941 1018962991997377757048807)
                    ·
                      rfl

theorem cell22_2976635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 5].length) (baseStart_2976635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976635 prefixEnd_2976635 := by exact prefixLift 2976635
  have htrace : WordTrace (prefixWord ++ tailWord_2976635) baseStart_2976635 baseEnd_2976635 := by
    simpa [prefixWord, tailWord_2976635, baseEnd_2976635] using wordTrace_append hprefix tailTrace_2976635
  have hstable : (prefixWord ++ tailWord_2976635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976635).length < 2 ^ (prefixWord ++ tailWord_2976635).sum := by decide
  have hdescent : baseEnd_2976635 < baseStart_2976635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976637 : List Nat := [1, 4, 1, 1, 2, 1, 5, 2, 5]
def baseStart_2976637 : Nat := 118140960795 + 2976637 * 2 ^ 59
def prefixEnd_2976637 : Nat := 4983230072969 + 3 ^ 40 * 2976637 * 2
def baseEnd_2976637 : Nat := 339654558879416806166267

theorem tailTrace_2976637 : CollatzResearch.WordTrace tailWord_2976637 prefixEnd_2976637 339654558879416806166267 := by
  unfold tailWord_2976637
  simp only [CollatzResearch.WordTrace]
  refine ⟨108566870517159992971376165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72377913678106661980917443 108566870517159992971376165)
  ·
    refine ⟨20356288221967498682133031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108566870517159992971376165 20356288221967498682133031)
    ·
      refine ⟨30534432332951248023199547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20356288221967498682133031 30534432332951248023199547)
      ·
        refine ⟨45801648499426872034799321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30534432332951248023199547 45801648499426872034799321)
        ·
          refine ⟨34351236374570154026099491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45801648499426872034799321 34351236374570154026099491)
          ·
            refine ⟨51526854561855231039149237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34351236374570154026099491 51526854561855231039149237)
            ·
              refine ⟨4830642615173927909920241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51526854561855231039149237 4830642615173927909920241)
              ·
                refine ⟨3622981961380445932440181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4830642615173927909920241 3622981961380445932440181)
                ·
                  refine ⟨339654558879416806166267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3622981961380445932440181 339654558879416806166267)
                  ·
                    rfl

theorem cell22_2976637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_2976637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976637 prefixEnd_2976637 := by exact prefixLift 2976637
  have htrace : WordTrace (prefixWord ++ tailWord_2976637) baseStart_2976637 baseEnd_2976637 := by
    simpa [prefixWord, tailWord_2976637, baseEnd_2976637] using wordTrace_append hprefix tailTrace_2976637
  have hstable : (prefixWord ++ tailWord_2976637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976637).length < 2 ^ (prefixWord ++ tailWord_2976637).sum := by decide
  have hdescent : baseEnd_2976637 < baseStart_2976637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976729 : List Nat := [1, 2, 1, 2, 5, 2, 2, 1, 2, 4]
def baseStart_2976729 : Nat := 118140960795 + 2976729 * 2 ^ 59
def prefixEnd_2976729 : Nat := 4983230072969 + 3 ^ 40 * 2976729 * 2
def baseEnd_2976729 : Nat := 1018995170118392845198519

theorem tailTrace_2976729 : CollatzResearch.WordTrace tailWord_2976729 prefixEnd_2976729 1018995170118392845198519 := by
  unfold tailWord_2976729
  simp only [CollatzResearch.WordTrace]
  refine ⟨108570226032826692683725241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72380150688551128455816827 108570226032826692683725241)
  ·
    refine ⟨81427669524620019512793931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108570226032826692683725241 81427669524620019512793931)
    ·
      refine ⟨122141504286930029269190897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81427669524620019512793931 122141504286930029269190897)
      ·
        refine ⟨91606128215197521951893173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122141504286930029269190897 91606128215197521951893173)
        ·
          refine ⟨8588074520174767682989985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91606128215197521951893173 8588074520174767682989985)
          ·
            refine ⟨6441055890131075762242489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8588074520174767682989985 6441055890131075762242489)
            ·
              refine ⟨4830791917598306821681867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6441055890131075762242489 4830791917598306821681867)
              ·
                refine ⟨7246187876397460232522801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4830791917598306821681867 7246187876397460232522801)
                ·
                  refine ⟨5434640907298095174392101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7246187876397460232522801 5434640907298095174392101)
                  ·
                    refine ⟨1018995170118392845198519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5434640907298095174392101 1018995170118392845198519)
                    ·
                      rfl

theorem cell22_2976729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 4].length) (baseStart_2976729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976729 prefixEnd_2976729 := by exact prefixLift 2976729
  have htrace : WordTrace (prefixWord ++ tailWord_2976729) baseStart_2976729 baseEnd_2976729 := by
    simpa [prefixWord, tailWord_2976729, baseEnd_2976729] using wordTrace_append hprefix tailTrace_2976729
  have hstable : (prefixWord ++ tailWord_2976729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976729).length < 2 ^ (prefixWord ++ tailWord_2976729).sum := by decide
  have hdescent : baseEnd_2976729 < baseStart_2976729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976750 : List Nat := [4, 1, 2, 1, 5, 1, 2, 2, 4]
def baseStart_2976750 : Nat := 118140960795 + 2976750 * 2 ^ 59
def prefixEnd_2976750 : Nat := 4983230072969 + 3 ^ 40 * 2976750 * 2
def baseEnd_2976750 : Nat := 339667452949185263474485

theorem tailTrace_2976750 : CollatzResearch.WordTrace tailWord_2976750 prefixEnd_2976750 339667452949185263474485 := by
  unfold tailWord_2976750
  simp only [CollatzResearch.WordTrace]
  refine ⟨13571373995718826658779963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72380661310500408846826469 13571373995718826658779963)
  ·
    refine ⟨20357060993578239988169945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13571373995718826658779963 20357060993578239988169945)
    ·
      refine ⟨15267795745183679991127459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20357060993578239988169945 15267795745183679991127459)
      ·
        refine ⟨22901693617775519986691189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15267795745183679991127459 22901693617775519986691189)
        ·
          refine ⟨2147033776666454998752299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22901693617775519986691189 2147033776666454998752299)
          ·
            refine ⟨3220550664999682498128449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2147033776666454998752299 3220550664999682498128449)
            ·
              refine ⟨2415412998749761873596337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3220550664999682498128449 2415412998749761873596337)
              ·
                refine ⟨1811559749062321405197253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2415412998749761873596337 1811559749062321405197253)
                ·
                  refine ⟨339667452949185263474485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1811559749062321405197253 339667452949185263474485)
                  ·
                    rfl

theorem cell22_2976750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_2976750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976750 prefixEnd_2976750 := by exact prefixLift 2976750
  have htrace : WordTrace (prefixWord ++ tailWord_2976750) baseStart_2976750 baseEnd_2976750 := by
    simpa [prefixWord, tailWord_2976750, baseEnd_2976750] using wordTrace_append hprefix tailTrace_2976750
  have hstable : (prefixWord ++ tailWord_2976750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976750).length < 2 ^ (prefixWord ++ tailWord_2976750).sum := by decide
  have hdescent : baseEnd_2976750 < baseStart_2976750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976804 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_2976804 : Nat := 118140960795 + 2976804 * 2 ^ 59
def prefixEnd_2976804 : Nat := 4983230072969 + 3 ^ 40 * 2976804 * 2
def baseEnd_2976804 : Nat := 1019020844151117649573289

theorem tailTrace_2976804 : CollatzResearch.WordTrace tailWord_2976804 prefixEnd_2976804 1019020844151117649573289 := by
  unfold tailWord_2976804
  simp only [CollatzResearch.WordTrace]
  refine ⟨54286480753777490246352733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72381974338369986995136977 54286480753777490246352733)
  ·
    refine ⟨20357430282666558842382275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54286480753777490246352733 20357430282666558842382275)
    ·
      refine ⟨30536145423999838263573413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20357430282666558842382275 30536145423999838263573413)
      ·
        refine ⟨5725527266999969674420015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30536145423999838263573413 5725527266999969674420015)
        ·
          refine ⟨8588290900499954511630023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5725527266999969674420015 8588290900499954511630023)
          ·
            refine ⟨12882436350749931767445035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8588290900499954511630023 12882436350749931767445035)
            ·
              refine ⟨19323654526124897651167553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12882436350749931767445035 19323654526124897651167553)
              ·
                refine ⟨14492740894593673238375665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19323654526124897651167553 14492740894593673238375665)
                ·
                  refine ⟨10869555670945254928781749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14492740894593673238375665 10869555670945254928781749)
                  ·
                    refine ⟨1019020844151117649573289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10869555670945254928781749 1019020844151117649573289)
                    ·
                      rfl

theorem cell22_2976804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_2976804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976804 prefixEnd_2976804 := by exact prefixLift 2976804
  have htrace : WordTrace (prefixWord ++ tailWord_2976804) baseStart_2976804 baseEnd_2976804 := by
    simpa [prefixWord, tailWord_2976804, baseEnd_2976804] using wordTrace_append hprefix tailTrace_2976804
  have hstable : (prefixWord ++ tailWord_2976804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976804).length < 2 ^ (prefixWord ++ tailWord_2976804).sum := by decide
  have hdescent : baseEnd_2976804 < baseStart_2976804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976849 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 4, 3]
def baseStart_2976849 : Nat := 118140960795 + 2976849 * 2 ^ 59
def prefixEnd_2976849 : Nat := 4983230072969 + 3 ^ 40 * 2976849 * 2
def baseEnd_2976849 : Nat := 1019036248570752532198151

theorem tailTrace_2976849 : CollatzResearch.WordTrace tailWord_2976849 prefixEnd_2976849 1019036248570752532198151 := by
  unfold tailWord_2976849
  simp only [CollatzResearch.WordTrace]
  refine ⟨108574602792391953178093601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72383068528261302118729067 108574602792391953178093601)
  ·
    refine ⟨81430952094293964883570201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108574602792391953178093601 81430952094293964883570201)
    ·
      refine ⟨61073214070720473662677651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81430952094293964883570201 61073214070720473662677651)
      ·
        refine ⟨91609821106080710494016477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61073214070720473662677651 91609821106080710494016477)
        ·
          refine ⟨34353682914780266435256179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91609821106080710494016477 34353682914780266435256179)
          ·
            refine ⟨51530524372170399652884269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34353682914780266435256179 51530524372170399652884269)
            ·
              refine ⟨19323946639563899869831601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51530524372170399652884269 19323946639563899869831601)
              ·
                refine ⟨14492959979672924902373701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19323946639563899869831601 14492959979672924902373701)
                ·
                  refine ⟨2717429996188673419195069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14492959979672924902373701 2717429996188673419195069)
                  ·
                    refine ⟨1019036248570752532198151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2717429996188673419195069 1019036248570752532198151)
                    ·
                      rfl

theorem cell22_2976849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_2976849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976849 prefixEnd_2976849 := by exact prefixLift 2976849
  have htrace : WordTrace (prefixWord ++ tailWord_2976849) baseStart_2976849 baseEnd_2976849 := by
    simpa [prefixWord, tailWord_2976849, baseEnd_2976849] using wordTrace_append hprefix tailTrace_2976849
  have hstable : (prefixWord ++ tailWord_2976849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976849).length < 2 ^ (prefixWord ++ tailWord_2976849).sum := by decide
  have hdescent : baseEnd_2976849 < baseStart_2976849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976864 : List Nat := [2, 1, 1, 3, 2, 2, 3, 2, 2, 4]
def baseStart_2976864 : Nat := 118140960795 + 2976864 * 2 ^ 59
def prefixEnd_2976864 : Nat := 4983230072969 + 3 ^ 40 * 2976864 * 2
def baseEnd_2976864 : Nat := 1019041383377297493073105

theorem tailTrace_2976864 : CollatzResearch.WordTrace tailWord_2976864 prefixEnd_2976864 1019041383377297493073105 := by
  unfold tailWord_2976864
  simp only [CollatzResearch.WordTrace]
  refine ⟨54287574943668805369944823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72383433258225073826593097 54287574943668805369944823)
  ·
    refine ⟨81431362415503208054917235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54287574943668805369944823 81431362415503208054917235)
    ·
      refine ⟨122147043623254812082375853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81431362415503208054917235 122147043623254812082375853)
      ·
        refine ⟨45805141358720554530890945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122147043623254812082375853 45805141358720554530890945)
        ·
          refine ⟨34353856019040415898168209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45805141358720554530890945 34353856019040415898168209)
          ·
            refine ⟨25765392014280311923626157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34353856019040415898168209 25765392014280311923626157)
            ·
              refine ⟨9662022005355116971359809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25765392014280311923626157 9662022005355116971359809)
              ·
                refine ⟨7246516504016337728519857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9662022005355116971359809 7246516504016337728519857)
                ·
                  refine ⟨5434887378012253296389893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7246516504016337728519857 5434887378012253296389893)
                  ·
                    refine ⟨1019041383377297493073105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5434887378012253296389893 1019041383377297493073105)
                    ·
                      rfl

theorem cell22_2976864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_2976864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976864 prefixEnd_2976864 := by exact prefixLift 2976864
  have htrace : WordTrace (prefixWord ++ tailWord_2976864) baseStart_2976864 baseEnd_2976864 := by
    simpa [prefixWord, tailWord_2976864, baseEnd_2976864] using wordTrace_append hprefix tailTrace_2976864
  have hstable : (prefixWord ++ tailWord_2976864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976864).length < 2 ^ (prefixWord ++ tailWord_2976864).sum := by decide
  have hdescent : baseEnd_2976864 < baseStart_2976864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976907 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 9]
def baseStart_2976907 : Nat := 118140960795 + 2976907 * 2 ^ 59
def prefixEnd_2976907 : Nat := 4983230072969 + 3 ^ 40 * 2976907 * 2
def baseEnd_2976907 : Nat := 339685367718686571415991

theorem tailTrace_2976907 : CollatzResearch.WordTrace tailWord_2976907 prefixEnd_2976907 339685367718686571415991 := by
  unfold tailWord_2976907
  simp only [CollatzResearch.WordTrace]
  refine ⟨108576718226181829083704975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72384478817454552722469983 108576718226181829083704975)
  ·
    refine ⟨162865077339272743625557463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108576718226181829083704975 162865077339272743625557463)
    ·
      refine ⟨244297616008909115438336195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162865077339272743625557463 244297616008909115438336195)
      ·
        refine ⟨366446424013363673157504293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244297616008909115438336195 366446424013363673157504293)
        ·
          refine ⟨68708704502505688717032055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 366446424013363673157504293 68708704502505688717032055)
          ·
            refine ⟨103063056753758533075548083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68708704502505688717032055 103063056753758533075548083)
            ·
              refine ⟨154594585130637799613322125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103063056753758533075548083 154594585130637799613322125)
              ·
                refine ⟨57972969423989174854995797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154594585130637799613322125 57972969423989174854995797)
                ·
                  refine ⟨339685367718686571415991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57972969423989174854995797 339685367718686571415991)
                  ·
                    rfl

theorem cell22_2976907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 9].length) (baseStart_2976907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976907 prefixEnd_2976907 := by exact prefixLift 2976907
  have htrace : WordTrace (prefixWord ++ tailWord_2976907) baseStart_2976907 baseEnd_2976907 := by
    simpa [prefixWord, tailWord_2976907, baseEnd_2976907] using wordTrace_append hprefix tailTrace_2976907
  have hstable : (prefixWord ++ tailWord_2976907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976907).length < 2 ^ (prefixWord ++ tailWord_2976907).sum := by decide
  have hdescent : baseEnd_2976907 < baseStart_2976907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976926 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_2976926 : Nat := 118140960795 + 2976926 * 2 ^ 59
def prefixEnd_2976926 : Nat := 4983230072969 + 3 ^ 40 * 2976926 * 2
def baseEnd_2976926 : Nat := 1019062607244349998022915

theorem tailTrace_2976926 : CollatzResearch.WordTrace tailWord_2976926 prefixEnd_2976926 1019062607244349998022915 := by
  unfold tailWord_2976926
  simp only [CollatzResearch.WordTrace]
  refine ⟨13572176401639124416080829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72384940808741996885764421 13572176401639124416080829)
  ·
    refine ⟨5089566150614671656030311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13572176401639124416080829 5089566150614671656030311)
    ·
      refine ⟨7634349225922007484045467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5089566150614671656030311 7634349225922007484045467)
      ·
        refine ⟨11451523838883011226068201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7634349225922007484045467 11451523838883011226068201)
        ·
          refine ⟨8588642879162258419551151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11451523838883011226068201 8588642879162258419551151)
          ·
            refine ⟨12882964318743387629326727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8588642879162258419551151 12882964318743387629326727)
            ·
              refine ⟨19324446478115081443990091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12882964318743387629326727 19324446478115081443990091)
              ·
                refine ⟨28986669717172622165985137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19324446478115081443990091 28986669717172622165985137)
                ·
                  refine ⟨21740002287879466624488853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28986669717172622165985137 21740002287879466624488853)
                  ·
                    refine ⟨1019062607244349998022915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21740002287879466624488853 1019062607244349998022915)
                    ·
                      rfl

theorem cell22_2976926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_2976926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976926 prefixEnd_2976926 := by exact prefixLift 2976926
  have htrace : WordTrace (prefixWord ++ tailWord_2976926) baseStart_2976926 baseEnd_2976926 := by
    simpa [prefixWord, tailWord_2976926, baseEnd_2976926] using wordTrace_append hprefix tailTrace_2976926
  have hstable : (prefixWord ++ tailWord_2976926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976926).length < 2 ^ (prefixWord ++ tailWord_2976926).sum := by decide
  have hdescent : baseEnd_2976926 < baseStart_2976926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976928 : List Nat := [2, 1, 1, 4, 2, 1, 3, 4, 1, 3]
def baseStart_2976928 : Nat := 118140960795 + 2976928 * 2 ^ 59
def prefixEnd_2976928 : Nat := 4983230072969 + 3 ^ 40 * 2976928 * 2
def baseEnd_2976928 : Nat := 1019063291885222659472909

theorem tailTrace_2976928 : CollatzResearch.WordTrace tailWord_2976928 prefixEnd_2976928 1019063291885222659472909 := by
  unfold tailWord_2976928
  simp only [CollatzResearch.WordTrace]
  refine ⟨54288742079552874835109719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72384989439403833113479625 54288742079552874835109719)
  ·
    refine ⟨81433113119329312252664579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54288742079552874835109719 81433113119329312252664579)
    ·
      refine ⟨122149669678993968378996869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81433113119329312252664579 122149669678993968378996869)
      ·
        refine ⟨22903063064811369071061913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122149669678993968378996869 22903063064811369071061913)
        ·
          refine ⟨17177297298608526803296435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22903063064811369071061913 17177297298608526803296435)
          ·
            refine ⟨25765945947912790204944653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17177297298608526803296435 25765945947912790204944653)
            ·
              refine ⟨9662229730467296326854245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25765945947912790204944653 9662229730467296326854245)
              ·
                refine ⟨1811668074462618061285171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9662229730467296326854245 1811668074462618061285171)
                ·
                  refine ⟨2717502111693927091927757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811668074462618061285171 2717502111693927091927757)
                  ·
                    refine ⟨1019063291885222659472909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2717502111693927091927757 1019063291885222659472909)
                    ·
                      rfl

theorem cell22_2976928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 1, 3].length) (baseStart_2976928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2976928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2976928 prefixEnd_2976928 := by exact prefixLift 2976928
  have htrace : WordTrace (prefixWord ++ tailWord_2976928) baseStart_2976928 baseEnd_2976928 := by
    simpa [prefixWord, tailWord_2976928, baseEnd_2976928] using wordTrace_append hprefix tailTrace_2976928
  have hstable : (prefixWord ++ tailWord_2976928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976928).length < 2 ^ (prefixWord ++ tailWord_2976928).sum := by decide
  have hdescent : baseEnd_2976928 < baseStart_2976928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977020 : List Nat := [2, 2, 2, 1, 5, 2, 1, 3, 4]
def baseStart_2977020 : Nat := 118140960795 + 2977020 * 2 ^ 59
def prefixEnd_2977020 : Nat := 4983230072969 + 3 ^ 40 * 2977020 * 2
def baseEnd_2977020 : Nat := 339698261788455028724209

theorem tailTrace_2977020 : CollatzResearch.WordTrace tailWord_2977020 prefixEnd_2977020 339698261788455028724209 := by
  unfold tailWord_2977020
  simp only [CollatzResearch.WordTrace]
  refine ⟨54290419837386224691284257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72387226449848299588379009 54290419837386224691284257)
  ·
    refine ⟨40717814878039668518463193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54290419837386224691284257 40717814878039668518463193)
    ·
      refine ⟨30538361158529751388847395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40717814878039668518463193 30538361158529751388847395)
      ·
        refine ⟨45807541737794627083271093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30538361158529751388847395 45807541737794627083271093)
        ·
          refine ⟨4294457037918246289056665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45807541737794627083271093 4294457037918246289056665)
          ·
            refine ⟨3220842778438684716792499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4294457037918246289056665 3220842778438684716792499)
            ·
              refine ⟨4831264167658027075188749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3220842778438684716792499 4831264167658027075188749)
              ·
                refine ⟨1811724062871760153195781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4831264167658027075188749 1811724062871760153195781)
                ·
                  refine ⟨339698261788455028724209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1811724062871760153195781 339698261788455028724209)
                  ·
                    rfl

theorem cell22_2977020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_2977020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977020 prefixEnd_2977020 := by exact prefixLift 2977020
  have htrace : WordTrace (prefixWord ++ tailWord_2977020) baseStart_2977020 baseEnd_2977020 := by
    simpa [prefixWord, tailWord_2977020, baseEnd_2977020] using wordTrace_append hprefix tailTrace_2977020
  have hstable : (prefixWord ++ tailWord_2977020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977020).length < 2 ^ (prefixWord ++ tailWord_2977020).sum := by decide
  have hdescent : baseEnd_2977020 < baseStart_2977020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977136 : List Nat := [2, 1, 1, 1, 4, 2, 1, 4, 1, 5]
def baseStart_2977136 : Nat := 118140960795 + 2977136 * 2 ^ 59
def prefixEnd_2977136 : Nat := 4983230072969 + 3 ^ 40 * 2977136 * 2
def baseEnd_2977136 : Nat := 1019134494535979450272271

theorem tailTrace_2977136 : CollatzResearch.WordTrace tailWord_2977136 prefixEnd_2977136 1019134494535979450272271 := by
  unfold tailWord_2977136
  simp only [CollatzResearch.WordTrace]
  refine ⟨54292535271176100596895631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72390047028234800795860841 54292535271176100596895631)
  ·
    refine ⟨81438802906764150895343447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54292535271176100596895631 81438802906764150895343447)
    ·
      refine ⟨122158204360146226343015171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81438802906764150895343447 122158204360146226343015171)
      ·
        refine ⟨183237306540219339514522757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122158204360146226343015171 183237306540219339514522757)
        ·
          refine ⟨34356994976291126158973017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183237306540219339514522757 34356994976291126158973017)
          ·
            refine ⟨25767746232218344619229763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34356994976291126158973017 25767746232218344619229763)
            ·
              refine ⟨38651619348327516928844645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25767746232218344619229763 38651619348327516928844645)
              ·
                refine ⟨7247178627811409424158371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38651619348327516928844645 7247178627811409424158371)
                ·
                  refine ⟨10870767941717114136237557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7247178627811409424158371 10870767941717114136237557)
                  ·
                    refine ⟨1019134494535979450272271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10870767941717114136237557 1019134494535979450272271)
                    ·
                      rfl

theorem cell22_2977136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_2977136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977136 prefixEnd_2977136 := by exact prefixLift 2977136
  have htrace : WordTrace (prefixWord ++ tailWord_2977136) baseStart_2977136 baseEnd_2977136 := by
    simpa [prefixWord, tailWord_2977136, baseEnd_2977136] using wordTrace_append hprefix tailTrace_2977136
  have hstable : (prefixWord ++ tailWord_2977136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977136).length < 2 ^ (prefixWord ++ tailWord_2977136).sum := by decide
  have hdescent : baseEnd_2977136 < baseStart_2977136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977183 : List Nat := [1, 1, 2, 5, 1, 2, 4, 6]
def baseStart_2977183 : Nat := 118140960795 + 2977183 * 2 ^ 59
def prefixEnd_2977183 : Nat := 4983230072969 + 3 ^ 40 * 2977183 * 2
def baseEnd_2977183 : Nat := 113238953732942999371903

theorem tailTrace_2977183 : CollatzResearch.WordTrace tailWord_2977183 prefixEnd_2977183 113238953732942999371903 := by
  unfold tailWord_2977183
  simp only [CollatzResearch.WordTrace]
  refine ⟨108586784773181928220752203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72391189848787952147168135 108586784773181928220752203)
  ·
    refine ⟨162880177159772892331128305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108586784773181928220752203 162880177159772892331128305)
    ·
      refine ⟨122160132869829669248346229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162880177159772892331128305 122160132869829669248346229)
      ·
        refine ⟨11452512456546531492032459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122160132869829669248346229 11452512456546531492032459)
        ·
          refine ⟨17178768684819797238048689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11452512456546531492032459 17178768684819797238048689)
          ·
            refine ⟨12884076513614847928536517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17178768684819797238048689 12884076513614847928536517)
            ·
              refine ⟨2415764346302783986600597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12884076513614847928536517 2415764346302783986600597)
              ·
                refine ⟨113238953732942999371903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2415764346302783986600597 113238953732942999371903)
                ·
                  rfl

theorem cell22_2977183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 6].length) (baseStart_2977183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977183 prefixEnd_2977183 := by exact prefixLift 2977183
  have htrace : WordTrace (prefixWord ++ tailWord_2977183) baseStart_2977183 baseEnd_2977183 := by
    simpa [prefixWord, tailWord_2977183, baseEnd_2977183] using wordTrace_append hprefix tailTrace_2977183
  have hstable : (prefixWord ++ tailWord_2977183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977183).length < 2 ^ (prefixWord ++ tailWord_2977183).sum := by decide
  have hdescent : baseEnd_2977183 < baseStart_2977183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977215 : List Nat := [1, 1, 2, 2, 2, 1, 1, 8, 1, 3]
def baseStart_2977215 : Nat := 118140960795 + 2977215 * 2 ^ 59
def prefixEnd_2977215 : Nat := 4983230072969 + 3 ^ 40 * 2977215 * 2
def baseEnd_2977215 : Nat := 1019161537850449577547029

theorem tailTrace_2977215 : CollatzResearch.WordTrace tailWord_2977215 prefixEnd_2977215 1019161537850449577547029 := by
  unfold tailWord_2977215
  simp only [CollatzResearch.WordTrace]
  refine ⟨108587951909065997685917099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72391967939377331790611399 108587951909065997685917099)
  ·
    refine ⟨162881927863598996528875649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108587951909065997685917099 162881927863598996528875649)
    ·
      refine ⟨122161445897699247396656737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162881927863598996528875649 122161445897699247396656737)
      ·
        refine ⟨91621084423274435547492553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122161445897699247396656737 91621084423274435547492553)
        ·
          refine ⟨68715813317455826660619415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91621084423274435547492553 68715813317455826660619415)
          ·
            refine ⟨103073719976183739990929123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68715813317455826660619415 103073719976183739990929123)
            ·
              refine ⟨154610579964275609986393685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103073719976183739990929123 154610579964275609986393685)
              ·
                refine ⟨1811842733956354804528051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 154610579964275609986393685 1811842733956354804528051)
                ·
                  refine ⟨2717764100934532206792077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811842733956354804528051 2717764100934532206792077)
                  ·
                    refine ⟨1019161537850449577547029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2717764100934532206792077 1019161537850449577547029)
                    ·
                      rfl

theorem cell22_2977215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 1, 3].length) (baseStart_2977215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977215 prefixEnd_2977215 := by exact prefixLift 2977215
  have htrace : WordTrace (prefixWord ++ tailWord_2977215) baseStart_2977215 baseEnd_2977215 := by
    simpa [prefixWord, tailWord_2977215, baseEnd_2977215] using wordTrace_append hprefix tailTrace_2977215
  have hstable : (prefixWord ++ tailWord_2977215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977215).length < 2 ^ (prefixWord ++ tailWord_2977215).sum := by decide
  have hdescent : baseEnd_2977215 < baseStart_2977215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977266 : List Nat := [3, 2, 1, 4, 1, 3, 2, 2, 1, 3]
def baseStart_2977266 : Nat := 118140960795 + 2977266 * 2 ^ 59
def prefixEnd_2977266 : Nat := 4983230072969 + 3 ^ 40 * 2977266 * 2
def baseEnd_2977266 : Nat := 1019178996192702444521873

theorem tailTrace_2977266 : CollatzResearch.WordTrace tailWord_2977266 prefixEnd_2977266 1019178996192702444521873 := by
  unfold tailWord_2977266
  simp only [CollatzResearch.WordTrace]
  refine ⟨27147453007970308349005913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72393208021254155597349101 27147453007970308349005913)
  ·
    refine ⟨20360589755977731261754435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27147453007970308349005913 20360589755977731261754435)
    ·
      refine ⟨30540884633966596892631653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20360589755977731261754435 30540884633966596892631653)
      ·
        refine ⟨5726415868868736917368435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30540884633966596892631653 5726415868868736917368435)
        ·
          refine ⟨8589623803303105376052653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5726415868868736917368435 8589623803303105376052653)
          ·
            refine ⟨3221108926238664516019745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8589623803303105376052653 3221108926238664516019745)
            ·
              refine ⟨2415831694678998387014809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3221108926238664516019745 2415831694678998387014809)
              ·
                refine ⟨1811873771009248790261107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2415831694678998387014809 1811873771009248790261107)
                ·
                  refine ⟨2717810656513873185391661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811873771009248790261107 2717810656513873185391661)
                  ·
                    refine ⟨1019178996192702444521873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2717810656513873185391661 1019178996192702444521873)
                    ·
                      rfl

theorem cell22_2977266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_2977266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977266 prefixEnd_2977266 := by exact prefixLift 2977266
  have htrace : WordTrace (prefixWord ++ tailWord_2977266) baseStart_2977266 baseEnd_2977266 := by
    simpa [prefixWord, tailWord_2977266, baseEnd_2977266] using wordTrace_append hprefix tailTrace_2977266
  have hstable : (prefixWord ++ tailWord_2977266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977266).length < 2 ^ (prefixWord ++ tailWord_2977266).sum := by decide
  have hdescent : baseEnd_2977266 < baseStart_2977266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977288 : List Nat := [2, 1, 3, 2, 1, 1, 3, 3, 1, 5]
def baseStart_2977288 : Nat := 118140960795 + 2977288 * 2 ^ 59
def prefixEnd_2977288 : Nat := 4983230072969 + 3 ^ 40 * 2977288 * 2
def baseEnd_2977288 : Nat := 1019186527242301720471805

theorem tailTrace_2977288 : CollatzResearch.WordTrace tailWord_2977288 prefixEnd_2977288 1019186527242301720471805 := by
  unfold tailWord_2977288
  simp only [CollatzResearch.WordTrace]
  refine ⟨54295307218900765576662259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72393742958534354102216345 54295307218900765576662259)
  ·
    refine ⟨81442960828351148364993389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54295307218900765576662259 81442960828351148364993389)
    ·
      refine ⟨30541110310631680636872521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81442960828351148364993389 30541110310631680636872521)
      ·
        refine ⟨22905832732973760477654391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30541110310631680636872521 22905832732973760477654391)
        ·
          refine ⟨34358749099460640716481587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22905832732973760477654391 34358749099460640716481587)
          ·
            refine ⟨51538123649190961074722381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34358749099460640716481587 51538123649190961074722381)
            ·
              refine ⟨19326796368446610403020893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51538123649190961074722381 19326796368446610403020893)
              ·
                refine ⟨7247548638167478901132835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19326796368446610403020893 7247548638167478901132835)
                ·
                  refine ⟨10871322957251218351699253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7247548638167478901132835 10871322957251218351699253)
                  ·
                    refine ⟨1019186527242301720471805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10871322957251218351699253 1019186527242301720471805)
                    ·
                      rfl

theorem cell22_2977288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_2977288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977288 prefixEnd_2977288 := by exact prefixLift 2977288
  have htrace : WordTrace (prefixWord ++ tailWord_2977288) baseStart_2977288 baseEnd_2977288 := by
    simpa [prefixWord, tailWord_2977288, baseEnd_2977288] using wordTrace_append hprefix tailTrace_2977288
  have hstable : (prefixWord ++ tailWord_2977288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977288).length < 2 ^ (prefixWord ++ tailWord_2977288).sum := by decide
  have hdescent : baseEnd_2977288 < baseStart_2977288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977384 : List Nat := [2, 1, 4, 3, 1, 3, 1, 1, 3, 3]
def baseStart_2977384 : Nat := 118140960795 + 2977384 * 2 ^ 59
def prefixEnd_2977384 : Nat := 4983230072969 + 3 ^ 40 * 2977384 * 2
def baseEnd_2977384 : Nat := 1019219390004189470071511

theorem tailTrace_2977384 : CollatzResearch.WordTrace tailWord_2977384 prefixEnd_2977384 1019219390004189470071511 := by
  unfold tailWord_2977384
  simp only [CollatzResearch.WordTrace]
  refine ⟨54297057922726869774409603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72396077230302493032546137 54297057922726869774409603)
  ·
    refine ⟨81445586884090304661614405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54297057922726869774409603 81445586884090304661614405)
    ·
      refine ⟨15271047540766932124052701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81445586884090304661614405 15271047540766932124052701)
      ·
        refine ⟨5726642827787599546519763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15271047540766932124052701 5726642827787599546519763)
        ·
          refine ⟨8589964241681399319779645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5726642827787599546519763 8589964241681399319779645)
          ·
            refine ⟨3221236590630524744917367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8589964241681399319779645 3221236590630524744917367)
            ·
              refine ⟨4831854885945787117376051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3221236590630524744917367 4831854885945787117376051)
              ·
                refine ⟨7247782328918680676064077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4831854885945787117376051 7247782328918680676064077)
                ·
                  refine ⟨2717918373344505253524029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7247782328918680676064077 2717918373344505253524029)
                  ·
                    refine ⟨1019219390004189470071511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2717918373344505253524029 1019219390004189470071511)
                    ·
                      rfl

theorem cell22_2977384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_2977384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977384 prefixEnd_2977384 := by exact prefixLift 2977384
  have htrace : WordTrace (prefixWord ++ tailWord_2977384) baseStart_2977384 baseEnd_2977384 := by
    simpa [prefixWord, tailWord_2977384, baseEnd_2977384] using wordTrace_append hprefix tailTrace_2977384
  have hstable : (prefixWord ++ tailWord_2977384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977384).length < 2 ^ (prefixWord ++ tailWord_2977384).sum := by decide
  have hdescent : baseEnd_2977384 < baseStart_2977384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977397 : List Nat := [1, 3, 4, 2, 1, 2, 1, 3, 5]
def baseStart_2977397 : Nat := 118140960795 + 2977397 * 2 ^ 59
def prefixEnd_2977397 : Nat := 4983230072969 + 3 ^ 40 * 2977397 * 2
def baseEnd_2977397 : Nat := 339741280056620589832157

theorem tailTrace_2977397 : CollatzResearch.WordTrace tailWord_2977397 prefixEnd_2977397 339741280056620589832157 := by
  unfold tailWord_2977397
  simp only [CollatzResearch.WordTrace]
  refine ⟨108594589994406642769042445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72396393329604428512694963 108594589994406642769042445)
  ·
    refine ⟨40722971247902491038390917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108594589994406642769042445 40722971247902491038390917)
    ·
      refine ⟨7635557108981717069698297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40722971247902491038390917 7635557108981717069698297)
      ·
        refine ⟨5726667831736287802273723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7635557108981717069698297 5726667831736287802273723)
        ·
          refine ⟨8590001747604431703410585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5726667831736287802273723 8590001747604431703410585)
          ·
            refine ⟨6442501310703323777557939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8590001747604431703410585 6442501310703323777557939)
            ·
              refine ⟨9663751966054985666336909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6442501310703323777557939 9663751966054985666336909)
              ·
                refine ⟨3623906987270619624876341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9663751966054985666336909 3623906987270619624876341)
                ·
                  refine ⟨339741280056620589832157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3623906987270619624876341 339741280056620589832157)
                  ·
                    rfl

theorem cell22_2977397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_2977397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977397 prefixEnd_2977397 := by exact prefixLift 2977397
  have htrace : WordTrace (prefixWord ++ tailWord_2977397) baseStart_2977397 baseEnd_2977397 := by
    simpa [prefixWord, tailWord_2977397, baseEnd_2977397] using wordTrace_append hprefix tailTrace_2977397
  have hstable : (prefixWord ++ tailWord_2977397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977397).length < 2 ^ (prefixWord ++ tailWord_2977397).sum := by decide
  have hdescent : baseEnd_2977397 < baseStart_2977397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977408 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 8]
def baseStart_2977408 : Nat := 118140960795 + 2977408 * 2 ^ 59
def prefixEnd_2977408 : Nat := 4983230072969 + 3 ^ 40 * 2977408 * 2
def baseEnd_2977408 : Nat := 339742535231553802490479

theorem tailTrace_2977408 : CollatzResearch.WordTrace tailWord_2977408 prefixEnd_2977408 339742535231553802490479 := by
  unfold tailWord_2977408
  simp only [CollatzResearch.WordTrace]
  refine ⟨54297495598683395823846439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72396660798244527765128585 54297495598683395823846439)
  ·
    refine ⟨81446243398025093735769659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54297495598683395823846439 81446243398025093735769659)
    ·
      refine ⟨122169365097037640603654489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81446243398025093735769659 122169365097037640603654489)
      ·
        refine ⟨91627023822778230452740867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122169365097037640603654489 91627023822778230452740867)
        ·
          refine ⟨137440535734167345679111301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91627023822778230452740867 137440535734167345679111301)
          ·
            refine ⟨25770100450156377314833369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137440535734167345679111301 25770100450156377314833369)
            ·
              refine ⟨19327575337617282986125027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25770100450156377314833369 19327575337617282986125027)
              ·
                refine ⟨28991363006425924479187541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19327575337617282986125027 28991363006425924479187541)
                ·
                  refine ⟨339742535231553802490479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28991363006425924479187541 339742535231553802490479)
                  ·
                    rfl

theorem cell22_2977408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 8].length) (baseStart_2977408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977408 prefixEnd_2977408 := by exact prefixLift 2977408
  have htrace : WordTrace (prefixWord ++ tailWord_2977408) baseStart_2977408 baseEnd_2977408 := by
    simpa [prefixWord, tailWord_2977408, baseEnd_2977408] using wordTrace_append hprefix tailTrace_2977408
  have hstable : (prefixWord ++ tailWord_2977408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977408).length < 2 ^ (prefixWord ++ tailWord_2977408).sum := by decide
  have hdescent : baseEnd_2977408 < baseStart_2977408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977478 : List Nat := [6, 1, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_2977478 : Nat := 118140960795 + 2977478 * 2 ^ 59
def prefixEnd_2977478 : Nat := 4983230072969 + 3 ^ 40 * 2977478 * 2
def baseEnd_2977478 : Nat := 1019251568125204558221223

theorem tailTrace_2977478 : CollatzResearch.WordTrace tailWord_2977478 prefixEnd_2977478 1019251568125204558221223 := by
  unfold tailWord_2977478
  simp only [CollatzResearch.WordTrace]
  refine ⟨3393673259597287300085659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72398362871408795735160725 3393673259597287300085659)
  ·
    refine ⟨5090509889395930950128489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3393673259597287300085659 5090509889395930950128489)
    ·
      refine ⟨3817882417046948212596367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5090509889395930950128489 3817882417046948212596367)
      ·
        refine ⟨5726823625570422318894551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3817882417046948212596367 5726823625570422318894551)
        ·
          refine ⟨8590235438355633478341827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5726823625570422318894551 8590235438355633478341827)
          ·
            refine ⟨12885353157533450217512741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8590235438355633478341827 12885353157533450217512741)
            ·
              refine ⟨2416003717037521915783639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12885353157533450217512741 2416003717037521915783639)
              ·
                refine ⟨3624005575556282873675459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2416003717037521915783639 3624005575556282873675459)
                ·
                  refine ⟨5436008363334424310513189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3624005575556282873675459 5436008363334424310513189)
                  ·
                    refine ⟨1019251568125204558221223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5436008363334424310513189 1019251568125204558221223)
                    ·
                      rfl

theorem cell22_2977478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_2977478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977478 prefixEnd_2977478 := by exact prefixLift 2977478
  have htrace : WordTrace (prefixWord ++ tailWord_2977478) baseStart_2977478 baseEnd_2977478 := by
    simpa [prefixWord, tailWord_2977478, baseEnd_2977478] using wordTrace_append hprefix tailTrace_2977478
  have hstable : (prefixWord ++ tailWord_2977478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977478).length < 2 ^ (prefixWord ++ tailWord_2977478).sum := by decide
  have hdescent : baseEnd_2977478 < baseStart_2977478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977515 : List Nat := [1, 1, 1, 1, 2, 4, 2, 5, 5]
def baseStart_2977515 : Nat := 118140960795 + 2977515 * 2 ^ 59
def prefixEnd_2977515 : Nat := 4983230072969 + 3 ^ 40 * 2977515 * 2
def baseEnd_2977515 : Nat := 339754744660449598348703

theorem tailTrace_2977515 : CollatzResearch.WordTrace tailWord_2977515 prefixEnd_2977515 339754744660449598348703 := by
  unfold tailWord_2977515
  simp only [CollatzResearch.WordTrace]
  refine ⟨108598893807979148921837999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72399262538652765947891999 108598893807979148921837999)
  ·
    refine ⟨162898340711968723382756999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108598893807979148921837999 162898340711968723382756999)
    ·
      refine ⟨244347511067953085074135499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162898340711968723382756999 244347511067953085074135499)
      ·
        refine ⟨366521266601929627611203249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244347511067953085074135499 366521266601929627611203249)
        ·
          refine ⟨274890949951447220708402437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366521266601929627611203249 274890949951447220708402437)
          ·
            refine ⟨51542053115896353882825457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 274890949951447220708402437 51542053115896353882825457)
            ·
              refine ⟨38656539836922265412119093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51542053115896353882825457 38656539836922265412119093)
              ·
                refine ⟨3624050609711462382386165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38656539836922265412119093 3624050609711462382386165)
                ·
                  refine ⟨339754744660449598348703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3624050609711462382386165 339754744660449598348703)
                  ·
                    rfl

theorem cell22_2977515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 5].length) (baseStart_2977515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977515 prefixEnd_2977515 := by exact prefixLift 2977515
  have htrace : WordTrace (prefixWord ++ tailWord_2977515) baseStart_2977515 baseEnd_2977515 := by
    simpa [prefixWord, tailWord_2977515, baseEnd_2977515] using wordTrace_append hprefix tailTrace_2977515
  have hstable : (prefixWord ++ tailWord_2977515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977515).length < 2 ^ (prefixWord ++ tailWord_2977515).sum := by decide
  have hdescent : baseEnd_2977515 < baseStart_2977515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977545 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 5, 4]
def baseStart_2977545 : Nat := 118140960795 + 2977545 * 2 ^ 59
def prefixEnd_2977545 : Nat := 4983230072969 + 3 ^ 40 * 2977545 * 2
def baseEnd_2977545 : Nat := 1019274503594438716796017

theorem tailTrace_2977545 : CollatzResearch.WordTrace tailWord_2977545 prefixEnd_2977545 1019274503594438716796017 := by
  unfold tailWord_2977545
  simp only [CollatzResearch.WordTrace]
  refine ⟨108599987997870464045430089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72399991998580309363620059 108599987997870464045430089)
  ·
    refine ⟨81449990998402848034072567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108599987997870464045430089 81449990998402848034072567)
    ·
      refine ⟨122174986497604272051108851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81449990998402848034072567 122174986497604272051108851)
      ·
        refine ⟨183262479746406408076663277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122174986497604272051108851 183262479746406408076663277)
        ·
          refine ⟨68723429904902403028748729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183262479746406408076663277 68723429904902403028748729)
          ·
            refine ⟨51542572428676802271561547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68723429904902403028748729 51542572428676802271561547)
            ·
              refine ⟨77313858643015203407342321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51542572428676802271561547 77313858643015203407342321)
              ·
                refine ⟨57985393982261402555506741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77313858643015203407342321 57985393982261402555506741)
                ·
                  refine ⟨5436130685837006489578757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57985393982261402555506741 5436130685837006489578757)
                  ·
                    refine ⟨1019274503594438716796017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5436130685837006489578757 1019274503594438716796017)
                    ·
                      rfl

theorem cell22_2977545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_2977545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977545 prefixEnd_2977545 := by exact prefixLift 2977545
  have htrace : WordTrace (prefixWord ++ tailWord_2977545) baseStart_2977545 baseEnd_2977545 := by
    simpa [prefixWord, tailWord_2977545, baseEnd_2977545] using wordTrace_append hprefix tailTrace_2977545
  have hstable : (prefixWord ++ tailWord_2977545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977545).length < 2 ^ (prefixWord ++ tailWord_2977545).sum := by decide
  have hdescent : baseEnd_2977545 < baseStart_2977545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977592 : List Nat := [2, 1, 2, 1, 3, 4, 1, 2, 1, 5]
def baseStart_2977592 : Nat := 118140960795 + 2977592 * 2 ^ 59
def prefixEnd_2977592 : Nat := 4983230072969 + 3 ^ 40 * 2977592 * 2
def baseEnd_2977592 : Nat := 1019290592654946260870873

theorem tailTrace_2977592 : CollatzResearch.WordTrace tailWord_2977592 prefixEnd_2977592 1019290592654946260870873 := by
  unfold tailWord_2977592
  simp only [CollatzResearch.WordTrace]
  refine ⟨54300851114350095536195515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72401134819133460714927353 54300851114350095536195515)
  ·
    refine ⟨81451276671525143304293273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54300851114350095536195515 81451276671525143304293273)
    ·
      refine ⟨61088457503643857478219955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81451276671525143304293273 61088457503643857478219955)
      ·
        refine ⟨91632686255465786217329933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61088457503643857478219955 91632686255465786217329933)
        ·
          refine ⟨34362257345799669831498725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91632686255465786217329933 34362257345799669831498725)
          ·
            refine ⟨6442923252337438093406011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34362257345799669831498725 6442923252337438093406011)
            ·
              refine ⟨9664384878506157140109017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6442923252337438093406011 9664384878506157140109017)
              ·
                refine ⟨7248288658879617855081763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9664384878506157140109017 7248288658879617855081763)
                ·
                  refine ⟨10872432988319426782622645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7248288658879617855081763 10872432988319426782622645)
                  ·
                    refine ⟨1019290592654946260870873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10872432988319426782622645 1019290592654946260870873)
                    ·
                      rfl

theorem cell22_2977592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_2977592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977592 prefixEnd_2977592 := by exact prefixLift 2977592
  have htrace : WordTrace (prefixWord ++ tailWord_2977592) baseStart_2977592 baseEnd_2977592 := by
    simpa [prefixWord, tailWord_2977592, baseEnd_2977592] using wordTrace_append hprefix tailTrace_2977592
  have hstable : (prefixWord ++ tailWord_2977592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977592).length < 2 ^ (prefixWord ++ tailWord_2977592).sum := by decide
  have hdescent : baseEnd_2977592 < baseStart_2977592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977607 : List Nat := [1, 1, 4, 1, 2, 1, 4, 2, 2, 4]
def baseStart_2977607 : Nat := 118140960795 + 2977607 * 2 ^ 59
def prefixEnd_2977607 : Nat := 4983230072969 + 3 ^ 40 * 2977607 * 2
def baseEnd_2977607 : Nat := 1019295727461491221745827

theorem tailTrace_2977607 : CollatzResearch.WordTrace tailWord_2977607 prefixEnd_2977607 1019295727461491221745827 := by
  unfold tailWord_2977607
  simp only [CollatzResearch.WordTrace]
  refine ⟨108602249323645848634187075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72401499549097232422791383 108602249323645848634187075)
  ·
    refine ⟨162903373985468772951280613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108602249323645848634187075 162903373985468772951280613)
    ·
      refine ⟨30544382622275394928365115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162903373985468772951280613 30544382622275394928365115)
      ·
        refine ⟨45816573933413092392547673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30544382622275394928365115 45816573933413092392547673)
        ·
          refine ⟨34362430450059819294410755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45816573933413092392547673 34362430450059819294410755)
          ·
            refine ⟨51543645675089728941616133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34362430450059819294410755 51543645675089728941616133)
            ·
              refine ⟨9664433564079324176553025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51543645675089728941616133 9664433564079324176553025)
              ·
                refine ⟨7248325173059493132414769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9664433564079324176553025 7248325173059493132414769)
                ·
                  refine ⟨5436243879794619849311077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7248325173059493132414769 5436243879794619849311077)
                  ·
                    refine ⟨1019295727461491221745827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5436243879794619849311077 1019295727461491221745827)
                    ·
                      rfl

theorem cell22_2977607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_2977607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977607 prefixEnd_2977607 := by exact prefixLift 2977607
  have htrace : WordTrace (prefixWord ++ tailWord_2977607) baseStart_2977607 baseEnd_2977607 := by
    simpa [prefixWord, tailWord_2977607, baseEnd_2977607] using wordTrace_append hprefix tailTrace_2977607
  have hstable : (prefixWord ++ tailWord_2977607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977607).length < 2 ^ (prefixWord ++ tailWord_2977607).sum := by decide
  have hdescent : baseEnd_2977607 < baseStart_2977607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977609 : List Nat := [1, 2, 1, 1, 2, 4, 4, 2, 2, 3]
def baseStart_2977609 : Nat := 118140960795 + 2977609 * 2 ^ 59
def prefixEnd_2977609 : Nat := 4983230072969 + 3 ^ 40 * 2977609 * 2
def baseEnd_2977609 : Nat := 1019296412102363883195821

theorem tailTrace_2977609 : CollatzResearch.WordTrace tailWord_2977609 prefixEnd_2977609 1019296412102363883195821 := by
  unfold tailWord_2977609
  simp only [CollatzResearch.WordTrace]
  refine ⟨108602322269638602975759881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72401548179759068650506587 108602322269638602975759881)
  ·
    refine ⟨81451741702228952231819911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108602322269638602975759881 81451741702228952231819911)
    ·
      refine ⟨122177612553343428347729867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81451741702228952231819911 122177612553343428347729867)
      ·
        refine ⟨183266418830015142521594801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122177612553343428347729867 183266418830015142521594801)
        ·
          refine ⟨137449814122511356891196101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183266418830015142521594801 137449814122511356891196101)
          ·
            refine ⟨25771840147970879417099269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137449814122511356891196101 25771840147970879417099269)
            ·
              refine ⟨4832220027744539890706113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25771840147970879417099269 4832220027744539890706113)
              ·
                refine ⟨3624165020808404918029585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4832220027744539890706113 3624165020808404918029585)
                ·
                  refine ⟨2718123765606303688522189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3624165020808404918029585 2718123765606303688522189)
                  ·
                    refine ⟨1019296412102363883195821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2718123765606303688522189 1019296412102363883195821)
                    ·
                      rfl

theorem cell22_2977609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 3].length) (baseStart_2977609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977609 prefixEnd_2977609 := by exact prefixLift 2977609
  have htrace : WordTrace (prefixWord ++ tailWord_2977609) baseStart_2977609 baseEnd_2977609 := by
    simpa [prefixWord, tailWord_2977609, baseEnd_2977609] using wordTrace_append hprefix tailTrace_2977609
  have hstable : (prefixWord ++ tailWord_2977609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977609).length < 2 ^ (prefixWord ++ tailWord_2977609).sum := by decide
  have hdescent : baseEnd_2977609 < baseStart_2977609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977667 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 7]
def baseStart_2977667 : Nat := 118140960795 + 2977667 * 2 ^ 59
def prefixEnd_2977667 : Nat := 4983230072969 + 3 ^ 40 * 2977667 * 2
def baseEnd_2977667 : Nat := 339772088895890355081881

theorem tailTrace_2977667 : CollatzResearch.WordTrace tailWord_2977667 prefixEnd_2977667 339772088895890355081881 := by
  unfold tailWord_2977667
  simp only [CollatzResearch.WordTrace]
  refine ⟨108604437703428478881371255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72402958468952319254247503 108604437703428478881371255)
  ·
    refine ⟨162906656555142718322056883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108604437703428478881371255 162906656555142718322056883)
    ·
      refine ⟨244359984832714077483085325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162906656555142718322056883 244359984832714077483085325)
      ·
        refine ⟨91634994312267779056156997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244359984832714077483085325 91634994312267779056156997)
        ·
          refine ⟨17181561433550208573029437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91634994312267779056156997 17181561433550208573029437)
          ·
            refine ⟨6443085537581328214886039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17181561433550208573029437 6443085537581328214886039)
            ·
              refine ⟨9664628306371992322329059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6443085537581328214886039 9664628306371992322329059)
              ·
                refine ⟨14496942459557988483493589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9664628306371992322329059 14496942459557988483493589)
                ·
                  refine ⟨339772088895890355081881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14496942459557988483493589 339772088895890355081881)
                  ·
                    rfl

theorem cell22_2977667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 7].length) (baseStart_2977667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977667 prefixEnd_2977667 := by exact prefixLift 2977667
  have htrace : WordTrace (prefixWord ++ tailWord_2977667) baseStart_2977667 baseEnd_2977667 := by
    simpa [prefixWord, tailWord_2977667, baseEnd_2977667] using wordTrace_append hprefix tailTrace_2977667
  have hstable : (prefixWord ++ tailWord_2977667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977667).length < 2 ^ (prefixWord ++ tailWord_2977667).sum := by decide
  have hdescent : baseEnd_2977667 < baseStart_2977667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977671 : List Nat := [1, 1, 4, 2, 4, 1, 2, 1, 3, 3]
def baseStart_2977671 : Nat := 118140960795 + 2977671 * 2 ^ 59
def prefixEnd_2977671 : Nat := 4983230072969 + 3 ^ 40 * 2977671 * 2
def baseEnd_2977671 : Nat := 1019317635969416388145631

theorem tailTrace_2977671 : CollatzResearch.WordTrace tailWord_2977671 prefixEnd_2977671 1019317635969416388145631 := by
  unfold tailWord_2977671
  simp only [CollatzResearch.WordTrace]
  refine ⟨108604583595413987564516867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72403055730275991709677911 108604583595413987564516867)
  ·
    refine ⟨162906875393120981346775301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108604583595413987564516867 162906875393120981346775301)
    ·
      refine ⟨30545039136210184002520369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162906875393120981346775301 30545039136210184002520369)
      ·
        refine ⟨22908779352157638001890277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30545039136210184002520369 22908779352157638001890277)
        ·
          refine ⟨4295396128529557125354427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22908779352157638001890277 4295396128529557125354427)
          ·
            refine ⟨6443094192794335688031641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4295396128529557125354427 6443094192794335688031641)
            ·
              refine ⟨4832320644595751766023731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6443094192794335688031641 4832320644595751766023731)
              ·
                refine ⟨7248480966893627649035597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4832320644595751766023731 7248480966893627649035597)
                ·
                  refine ⟨2718180362585110368388349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7248480966893627649035597 2718180362585110368388349)
                  ·
                    refine ⟨1019317635969416388145631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2718180362585110368388349 1019317635969416388145631)
                    ·
                      rfl

theorem cell22_2977671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_2977671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977671 prefixEnd_2977671 := by exact prefixLift 2977671
  have htrace : WordTrace (prefixWord ++ tailWord_2977671) baseStart_2977671 baseEnd_2977671 := by
    simpa [prefixWord, tailWord_2977671, baseEnd_2977671] using wordTrace_append hprefix tailTrace_2977671
  have hstable : (prefixWord ++ tailWord_2977671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977671).length < 2 ^ (prefixWord ++ tailWord_2977671).sum := by decide
  have hdescent : baseEnd_2977671 < baseStart_2977671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977759 : List Nat := [1, 1, 2, 3, 4, 1, 1, 3, 2, 4]
def baseStart_2977759 : Nat := 118140960795 + 2977759 * 2 ^ 59
def prefixEnd_2977759 : Nat := 4983230072969 + 3 ^ 40 * 2977759 * 2
def baseEnd_2977759 : Nat := 1019347760167813491945361

theorem tailTrace_2977759 : CollatzResearch.WordTrace tailWord_2977759 prefixEnd_2977759 1019347760167813491945361 := by
  unfold tailWord_2977759
  simp only [CollatzResearch.WordTrace]
  refine ⟨108607793219095178593720331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72405195479396785729146887 108607793219095178593720331)
  ·
    refine ⟨162911689828642767890580497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108607793219095178593720331 162911689828642767890580497)
    ·
      refine ⟨122183767371482075917935373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162911689828642767890580497 122183767371482075917935373)
      ·
        refine ⟨45818912764305778469225765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122183767371482075917935373 45818912764305778469225765)
        ·
          refine ⟨8591046143307333462979831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45818912764305778469225765 8591046143307333462979831)
          ·
            refine ⟨12886569214961000194469747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8591046143307333462979831 12886569214961000194469747)
            ·
              refine ⟨19329853822441500291704621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12886569214961000194469747 19329853822441500291704621)
              ·
                refine ⟨7248695183415562609389233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19329853822441500291704621 7248695183415562609389233)
                ·
                  refine ⟨5436521387561671957041925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7248695183415562609389233 5436521387561671957041925)
                  ·
                    refine ⟨1019347760167813491945361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5436521387561671957041925 1019347760167813491945361)
                    ·
                      rfl

theorem cell22_2977759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_2977759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977759 prefixEnd_2977759 := by exact prefixLift 2977759
  have htrace : WordTrace (prefixWord ++ tailWord_2977759) baseStart_2977759 baseEnd_2977759 := by
    simpa [prefixWord, tailWord_2977759, baseEnd_2977759] using wordTrace_append hprefix tailTrace_2977759
  have hstable : (prefixWord ++ tailWord_2977759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977759).length < 2 ^ (prefixWord ++ tailWord_2977759).sum := by decide
  have hdescent : baseEnd_2977759 < baseStart_2977759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977787 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 2, 6]
def baseStart_2977787 : Nat := 118140960795 + 2977787 * 2 ^ 59
def prefixEnd_2977787 : Nat := 4983230072969 + 3 ^ 40 * 2977787 * 2
def baseEnd_2977787 : Nat := 1019357345140030752245275

theorem tailTrace_2977787 : CollatzResearch.WordTrace tailWord_2977787 prefixEnd_2977787 1019357345140030752245275 := by
  unfold tailWord_2977787
  simp only [CollatzResearch.WordTrace]
  refine ⟨108608814462993739375739615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72405876308662492917159743 108608814462993739375739615)
  ·
    refine ⟨162913221694490609063609423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108608814462993739375739615 162913221694490609063609423)
    ·
      refine ⟨244369832541735913595414135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162913221694490609063609423 244369832541735913595414135)
      ·
        refine ⟨366554748812603870393121203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244369832541735913595414135 366554748812603870393121203)
        ·
          refine ⟨549832123218905805589681805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366554748812603870393121203 549832123218905805589681805)
          ·
            refine ⟨206187046207089677096130677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 549832123218905805589681805 206187046207089677096130677)
            ·
              refine ⟨19330035581914657227762251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 206187046207089677096130677 19330035581914657227762251)
              ·
                refine ⟨28995053372871985841643377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19330035581914657227762251 28995053372871985841643377)
                ·
                  refine ⟨21746290029653989381232533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28995053372871985841643377 21746290029653989381232533)
                  ·
                    refine ⟨1019357345140030752245275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21746290029653989381232533 1019357345140030752245275)
                    ·
                      rfl

theorem cell22_2977787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 6].length) (baseStart_2977787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977787 prefixEnd_2977787 := by exact prefixLift 2977787
  have htrace : WordTrace (prefixWord ++ tailWord_2977787) baseStart_2977787 baseEnd_2977787 := by
    simpa [prefixWord, tailWord_2977787, baseEnd_2977787] using wordTrace_append hprefix tailTrace_2977787
  have hstable : (prefixWord ++ tailWord_2977787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977787).length < 2 ^ (prefixWord ++ tailWord_2977787).sum := by decide
  have hdescent : baseEnd_2977787 < baseStart_2977787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977806 : List Nat := [4, 1, 1, 2, 2, 1, 3, 2, 3, 3]
def baseStart_2977806 : Nat := 118140960795 + 2977806 * 2 ^ 59
def prefixEnd_2977806 : Nat := 4983230072969 + 3 ^ 40 * 2977806 * 2
def baseEnd_2977806 : Nat := 1019363849228321036020217

theorem tailTrace_2977806 : CollatzResearch.WordTrace tailWord_2977806 prefixEnd_2977806 1019363849228321036020217 := by
  unfold tailWord_2977806
  simp only [CollatzResearch.WordTrace]
  refine ⟨13576188431240613202585159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72406338299949937080454181 13576188431240613202585159)
  ·
    refine ⟨20364282646860919803877739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13576188431240613202585159 20364282646860919803877739)
    ·
      refine ⟨30546423970291379705816609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20364282646860919803877739 30546423970291379705816609)
      ·
        refine ⟨22909817977718534779362457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30546423970291379705816609 22909817977718534779362457)
        ·
          refine ⟨17182363483288901084521843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22909817977718534779362457 17182363483288901084521843)
          ·
            refine ⟨25773545224933351626782765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17182363483288901084521843 25773545224933351626782765)
            ·
              refine ⟨9665079459350006860043537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25773545224933351626782765 9665079459350006860043537)
              ·
                refine ⟨7248809594512505145032653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9665079459350006860043537 7248809594512505145032653)
                ·
                  refine ⟨2718303597942189429387245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7248809594512505145032653 2718303597942189429387245)
                  ·
                    refine ⟨1019363849228321036020217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2718303597942189429387245 1019363849228321036020217)
                    ·
                      rfl

theorem cell22_2977806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_2977806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977806 prefixEnd_2977806 := by exact prefixLift 2977806
  have htrace : WordTrace (prefixWord ++ tailWord_2977806) baseStart_2977806 baseEnd_2977806 := by
    simpa [prefixWord, tailWord_2977806, baseEnd_2977806] using wordTrace_append hprefix tailTrace_2977806
  have hstable : (prefixWord ++ tailWord_2977806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977806).length < 2 ^ (prefixWord ++ tailWord_2977806).sum := by decide
  have hdescent : baseEnd_2977806 < baseStart_2977806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977817 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 3, 7]
def baseStart_2977817 : Nat := 118140960795 + 2977817 * 2 ^ 59
def prefixEnd_2977817 : Nat := 4983230072969 + 3 ^ 40 * 2977817 * 2
def baseEnd_2977817 : Nat := 1019367614753120673995183

theorem tailTrace_2977817 : CollatzResearch.WordTrace tailWord_2977817 prefixEnd_2977817 1019367614753120673995183 := by
  unfold tailWord_2977817
  simp only [CollatzResearch.WordTrace]
  refine ⟨108609908652885054499331705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72406605768590036332887803 108609908652885054499331705)
  ·
    refine ⟨81457431489663790874498779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108609908652885054499331705 81457431489663790874498779)
    ·
      refine ⟨122186147234495686311748169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81457431489663790874498779 122186147234495686311748169)
      ·
        refine ⟨91639610425871764733811127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122186147234495686311748169 91639610425871764733811127)
        ·
          refine ⟨137459415638807647100716691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91639610425871764733811127 137459415638807647100716691)
          ·
            refine ⟨206189123458211470651075037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137459415638807647100716691 206189123458211470651075037)
            ·
              refine ⟨77320921296829301494153139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206189123458211470651075037 77320921296829301494153139)
              ·
                refine ⟨115981381945243952241229709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77320921296829301494153139 115981381945243952241229709)
                ·
                  refine ⟨43493018229466482090461141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115981381945243952241229709 43493018229466482090461141)
                  ·
                    refine ⟨1019367614753120673995183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43493018229466482090461141 1019367614753120673995183)
                    ·
                      rfl

theorem cell22_2977817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_2977817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977817 prefixEnd_2977817 := by exact prefixLift 2977817
  have htrace : WordTrace (prefixWord ++ tailWord_2977817) baseStart_2977817 baseEnd_2977817 := by
    simpa [prefixWord, tailWord_2977817, baseEnd_2977817] using wordTrace_append hprefix tailTrace_2977817
  have hstable : (prefixWord ++ tailWord_2977817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977817).length < 2 ^ (prefixWord ++ tailWord_2977817).sum := by decide
  have hdescent : baseEnd_2977817 < baseStart_2977817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977823 : List Nat := [1, 1, 2, 4, 1, 2, 4, 3, 1, 3]
def baseStart_2977823 : Nat := 118140960795 + 2977823 * 2 ^ 59
def prefixEnd_2977823 : Nat := 4983230072969 + 3 ^ 40 * 2977823 * 2
def baseEnd_2977823 : Nat := 1019369668675738658345165

theorem tailTrace_2977823 : CollatzResearch.WordTrace tailWord_2977823 prefixEnd_2977823 1019369668675738658345165 := by
  unfold tailWord_2977823
  simp only [CollatzResearch.WordTrace]
  refine ⟨108610127490863317524050123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72406751660575545016033415 108610127490863317524050123)
  ·
    refine ⟨162915191236294976286075185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108610127490863317524050123 162915191236294976286075185)
    ·
      refine ⟨122186393427221232214556389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162915191236294976286075185 122186393427221232214556389)
      ·
        refine ⟨22909948767603981040229323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122186393427221232214556389 22909948767603981040229323)
        ·
          refine ⟨34364923151405971560343985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22909948767603981040229323 34364923151405971560343985)
          ·
            refine ⟨25773692363554478670257989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34364923151405971560343985 25773692363554478670257989)
            ·
              refine ⟨4832567318166464750673373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25773692363554478670257989 4832567318166464750673373)
              ·
                refine ⟨1812212744312424281502515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4832567318166464750673373 1812212744312424281502515)
                ·
                  refine ⟨2718319116468636422253773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1812212744312424281502515 2718319116468636422253773)
                  ·
                    refine ⟨1019369668675738658345165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2718319116468636422253773 1019369668675738658345165)
                    ·
                      rfl

theorem cell22_2977823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 1, 3].length) (baseStart_2977823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977823 prefixEnd_2977823 := by exact prefixLift 2977823
  have htrace : WordTrace (prefixWord ++ tailWord_2977823) baseStart_2977823 baseEnd_2977823 := by
    simpa [prefixWord, tailWord_2977823, baseEnd_2977823] using wordTrace_append hprefix tailTrace_2977823
  have hstable : (prefixWord ++ tailWord_2977823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977823).length < 2 ^ (prefixWord ++ tailWord_2977823).sum := by decide
  have hdescent : baseEnd_2977823 < baseStart_2977823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977879 : List Nat := [1, 1, 3, 2, 2, 1, 2, 4, 1, 5]
def baseStart_2977879 : Nat := 118140960795 + 2977879 * 2 ^ 59
def prefixEnd_2977879 : Nat := 4983230072969 + 3 ^ 40 * 2977879 * 2
def baseEnd_2977879 : Nat := 1019388838620173178944993

theorem tailTrace_2977879 : CollatzResearch.WordTrace tailWord_2977879 prefixEnd_2977879 1019388838620173178944993 := by
  unfold tailWord_2977879
  simp only [CollatzResearch.WordTrace]
  refine ⟨108612169978660439088088691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72408113319106959392059127 108612169978660439088088691)
  ·
    refine ⟨162918254967990658632133037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108612169978660439088088691 162918254967990658632133037)
    ·
      refine ⟨61094345612996496987049889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162918254967990658632133037 61094345612996496987049889)
      ·
        refine ⟨45820759209747372740287417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61094345612996496987049889 45820759209747372740287417)
        ·
          refine ⟨34365569407310529555215563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45820759209747372740287417 34365569407310529555215563)
          ·
            refine ⟨51548354110965794332823345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34365569407310529555215563 51548354110965794332823345)
            ·
              refine ⟨38661265583224345749617509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51548354110965794332823345 38661265583224345749617509)
              ·
                refine ⟨7248987296854564828053283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38661265583224345749617509 7248987296854564828053283)
                ·
                  refine ⟨10873480945281847242079925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7248987296854564828053283 10873480945281847242079925)
                  ·
                    refine ⟨1019388838620173178944993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10873480945281847242079925 1019388838620173178944993)
                    ·
                      rfl

theorem cell22_2977879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_2977879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977879 prefixEnd_2977879 := by exact prefixLift 2977879
  have htrace : WordTrace (prefixWord ++ tailWord_2977879) baseStart_2977879 baseEnd_2977879 := by
    simpa [prefixWord, tailWord_2977879, baseEnd_2977879] using wordTrace_append hprefix tailTrace_2977879
  have hstable : (prefixWord ++ tailWord_2977879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977879).length < 2 ^ (prefixWord ++ tailWord_2977879).sum := by decide
  have hdescent : baseEnd_2977879 < baseStart_2977879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977898 : List Nat := [3, 1, 3, 2, 3, 2, 1, 1, 6]
def baseStart_2977898 : Nat := 118140960795 + 2977898 * 2 ^ 59
def prefixEnd_2977898 : Nat := 4983230072969 + 3 ^ 40 * 2977898 * 2
def baseEnd_2977898 : Nat := 339798447569487820906645

theorem tailTrace_2977898 : CollatzResearch.WordTrace tailWord_2977898 prefixEnd_2977898 339798447569487820906645 := by
  unfold tailWord_2977898
  simp only [CollatzResearch.WordTrace]
  refine ⟨27153215741397901333257587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72408575310394403555353565 27153215741397901333257587)
  ·
    refine ⟨40729823612096851999886381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27153215741397901333257587 40729823612096851999886381)
    ·
      refine ⟨15273683854536319499957393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40729823612096851999886381 15273683854536319499957393)
      ·
        refine ⟨11455262890902239624968045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15273683854536319499957393 11455262890902239624968045)
        ·
          refine ⟨4295723584088339859363017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11455262890902239624968045 4295723584088339859363017)
          ·
            refine ⟨3221792688066254894522263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4295723584088339859363017 3221792688066254894522263)
            ·
              refine ⟨4832689032099382341783395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3221792688066254894522263 4832689032099382341783395)
              ·
                refine ⟨7249033548149073512675093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4832689032099382341783395 7249033548149073512675093)
                ·
                  refine ⟨339798447569487820906645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7249033548149073512675093 339798447569487820906645)
                  ·
                    rfl

theorem cell22_2977898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_2977898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977898 prefixEnd_2977898 := by exact prefixLift 2977898
  have htrace : WordTrace (prefixWord ++ tailWord_2977898) baseStart_2977898 baseEnd_2977898 := by
    simpa [prefixWord, tailWord_2977898, baseEnd_2977898] using wordTrace_append hprefix tailTrace_2977898
  have hstable : (prefixWord ++ tailWord_2977898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977898).length < 2 ^ (prefixWord ++ tailWord_2977898).sum := by decide
  have hdescent : baseEnd_2977898 < baseStart_2977898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977913 : List Nat := [1, 2, 1, 3, 4, 2, 1, 3, 2, 3]
def baseStart_2977913 : Nat := 118140960795 + 2977913 * 2 ^ 59
def prefixEnd_2977913 : Nat := 4983230072969 + 3 ^ 40 * 2977913 * 2
def baseEnd_2977913 : Nat := 1019400477515008423594889

theorem tailTrace_2977913 : CollatzResearch.WordTrace tailWord_2977913 prefixEnd_2977913 1019400477515008423594889 := by
  unfold tailWord_2977913
  simp only [CollatzResearch.WordTrace]
  refine ⟨108613410060537262894826393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72408940040358175263217595 108613410060537262894826393)
  ·
    refine ⟨81460057545402947171119795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108613410060537262894826393 81460057545402947171119795)
    ·
      refine ⟨122190086318104420756679693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81460057545402947171119795 122190086318104420756679693)
      ·
        refine ⟨45821282369289157783754885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122190086318104420756679693 45821282369289157783754885)
        ·
          refine ⟨8591490444241717084454041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45821282369289157783754885 8591490444241717084454041)
          ·
            refine ⟨6443617833181287813340531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8591490444241717084454041 6443617833181287813340531)
            ·
              refine ⟨9665426749771931720010797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6443617833181287813340531 9665426749771931720010797)
              ·
                refine ⟨3624535031164474395004049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9665426749771931720010797 3624535031164474395004049)
                ·
                  refine ⟨2718401273373355796253037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3624535031164474395004049 2718401273373355796253037)
                  ·
                    refine ⟨1019400477515008423594889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2718401273373355796253037 1019400477515008423594889)
                    ·
                      rfl

theorem cell22_2977913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 3].length) (baseStart_2977913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977913 prefixEnd_2977913 := by exact prefixLift 2977913
  have htrace : WordTrace (prefixWord ++ tailWord_2977913) baseStart_2977913 baseEnd_2977913 := by
    simpa [prefixWord, tailWord_2977913, baseEnd_2977913] using wordTrace_append hprefix tailTrace_2977913
  have hstable : (prefixWord ++ tailWord_2977913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977913).length < 2 ^ (prefixWord ++ tailWord_2977913).sum := by decide
  have hdescent : baseEnd_2977913 < baseStart_2977913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977928 : List Nat := [2, 1, 3, 4, 1, 2, 2, 1, 2, 4]
def baseStart_2977928 : Nat := 118140960795 + 2977928 * 2 ^ 59
def prefixEnd_2977928 : Nat := 4983230072969 + 3 ^ 40 * 2977928 * 2
def baseEnd_2977928 : Nat := 1019405612321553384469843

theorem tailTrace_2977928 : CollatzResearch.WordTrace tailWord_2977928 prefixEnd_2977928 1019405612321553384469843 := by
  unfold tailWord_2977928
  simp only [CollatzResearch.WordTrace]
  refine ⟨54306978577741460228311219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72409304770321946971081625 54306978577741460228311219)
  ·
    refine ⟨81460467866612190342466829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54306978577741460228311219 81460467866612190342466829)
    ·
      refine ⟨30547675449979571378425061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81460467866612190342466829 30547675449979571378425061)
      ·
        refine ⟨5727689146871169633454699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30547675449979571378425061 5727689146871169633454699)
        ·
          refine ⟨8591533720306754450182049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5727689146871169633454699 8591533720306754450182049)
          ·
            refine ⟨6443650290230065837636537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8591533720306754450182049 6443650290230065837636537)
            ·
              refine ⟨4832737717672549378227403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6443650290230065837636537 4832737717672549378227403)
              ·
                refine ⟨7249106576508824067341105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4832737717672549378227403 7249106576508824067341105)
                ·
                  refine ⟨5436829932381618050505829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7249106576508824067341105 5436829932381618050505829)
                  ·
                    refine ⟨1019405612321553384469843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5436829932381618050505829 1019405612321553384469843)
                    ·
                      rfl

theorem cell22_2977928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_2977928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977928 prefixEnd_2977928 := by exact prefixLift 2977928
  have htrace : WordTrace (prefixWord ++ tailWord_2977928) baseStart_2977928 baseEnd_2977928 := by
    simpa [prefixWord, tailWord_2977928, baseEnd_2977928] using wordTrace_append hprefix tailTrace_2977928
  have hstable : (prefixWord ++ tailWord_2977928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977928).length < 2 ^ (prefixWord ++ tailWord_2977928).sum := by decide
  have hdescent : baseEnd_2977928 < baseStart_2977928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977999 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 8]
def baseStart_2977999 : Nat := 118140960795 + 2977999 * 2 ^ 59
def prefixEnd_2977999 : Nat := 4983230072969 + 3 ^ 40 * 2977999 * 2
def baseEnd_2977999 : Nat := 339809972357510955314875

theorem tailTrace_2977999 : CollatzResearch.WordTrace tailWord_2977999 prefixEnd_2977999 339809972357510955314875 := by
  unfold tailWord_2977999
  simp only [CollatzResearch.WordTrace]
  refine ⟨108616546738225699582457051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72411031158817133054971367 108616546738225699582457051)
  ·
    refine ⟨162924820107338549373685577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108616546738225699582457051 162924820107338549373685577)
    ·
      refine ⟨122193615080503912030264183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162924820107338549373685577 122193615080503912030264183)
      ·
        refine ⟨183290422620755868045396275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122193615080503912030264183 183290422620755868045396275)
        ·
          refine ⟨274935633931133802068094413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183290422620755868045396275 274935633931133802068094413)
          ·
            refine ⟨103100862724175175775535405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 274935633931133802068094413 103100862724175175775535405)
            ·
              refine ⟨38662823521565690915825777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103100862724175175775535405 38662823521565690915825777)
              ·
                refine ⟨28997117641174268186869333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38662823521565690915825777 28997117641174268186869333)
                ·
                  refine ⟨339809972357510955314875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28997117641174268186869333 339809972357510955314875)
                  ·
                    rfl

theorem cell22_2977999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 8].length) (baseStart_2977999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2977999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2977999 prefixEnd_2977999 := by exact prefixLift 2977999
  have htrace : WordTrace (prefixWord ++ tailWord_2977999) baseStart_2977999 baseEnd_2977999 := by
    simpa [prefixWord, tailWord_2977999, baseEnd_2977999] using wordTrace_append hprefix tailTrace_2977999
  have hstable : (prefixWord ++ tailWord_2977999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977999).length < 2 ^ (prefixWord ++ tailWord_2977999).sum := by decide
  have hdescent : baseEnd_2977999 < baseStart_2977999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978005 : List Nat := [1, 3, 2, 4, 2, 2, 1, 2, 5]
def baseStart_2978005 : Nat := 118140960795 + 2978005 * 2 ^ 59
def prefixEnd_2978005 : Nat := 4983230072969 + 3 ^ 40 * 2978005 * 2
def baseEnd_2978005 : Nat := 339810656998383616764869

theorem tailTrace_2978005 : CollatzResearch.WordTrace tailWord_2978005 prefixEnd_2978005 339810656998383616764869 := by
  unfold tailWord_2978005
  simp only [CollatzResearch.WordTrace]
  refine ⟨108616765576203962607175469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72411177050802641738116979 108616765576203962607175469)
  ·
    refine ⟨40731287091076485977690801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108616765576203962607175469 40731287091076485977690801)
    ·
      refine ⟨30548465318307364483268101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40731287091076485977690801 30548465318307364483268101)
      ·
        refine ⟨5727837247182630840612769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30548465318307364483268101 5727837247182630840612769)
        ·
          refine ⟨4295877935386973130459577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5727837247182630840612769 4295877935386973130459577)
          ·
            refine ⟨3221908451540229847844683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4295877935386973130459577 3221908451540229847844683)
            ·
              refine ⟨4832862677310344771767025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3221908451540229847844683 4832862677310344771767025)
              ·
                refine ⟨3624647007982758578825269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4832862677310344771767025 3624647007982758578825269)
                ·
                  refine ⟨339810656998383616764869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3624647007982758578825269 339810656998383616764869)
                  ·
                    rfl

theorem cell22_2978005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_2978005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978005 prefixEnd_2978005 := by exact prefixLift 2978005
  have htrace : WordTrace (prefixWord ++ tailWord_2978005) baseStart_2978005 baseEnd_2978005 := by
    simpa [prefixWord, tailWord_2978005, baseEnd_2978005] using wordTrace_append hprefix tailTrace_2978005
  have hstable : (prefixWord ++ tailWord_2978005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978005).length < 2 ^ (prefixWord ++ tailWord_2978005).sum := by decide
  have hdescent : baseEnd_2978005 < baseStart_2978005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978016 : List Nat := [2, 1, 1, 3, 1, 3, 4, 1, 6]
def baseStart_2978016 : Nat := 118140960795 + 2978016 * 2 ^ 59
def prefixEnd_2978016 : Nat := 4983230072969 + 3 ^ 40 * 2978016 * 2
def baseEnd_2978016 : Nat := 339811912173316829423191

theorem tailTrace_2978016 : CollatzResearch.WordTrace tailWord_2978016 prefixEnd_2978016 339811912173316829423191 := by
  unfold tailWord_2978016
  simp only [CollatzResearch.WordTrace]
  refine ⟨54308583389582055742912951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72411444519442740990550601 54308583389582055742912951)
  ·
    refine ⟨81462875084373083614369427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54308583389582055742912951 81462875084373083614369427)
    ·
      refine ⟨122194312626559625421554141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81462875084373083614369427 122194312626559625421554141)
      ·
        refine ⟨45822867234959859533082803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122194312626559625421554141 45822867234959859533082803)
        ·
          refine ⟨68734300852439789299624205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45822867234959859533082803 68734300852439789299624205)
          ·
            refine ⟨25775362819664920987359077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68734300852439789299624205 25775362819664920987359077)
            ·
              refine ⟨4832880528687172685129827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25775362819664920987359077 4832880528687172685129827)
              ·
                refine ⟨7249320793030759027694741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4832880528687172685129827 7249320793030759027694741)
                ·
                  refine ⟨339811912173316829423191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7249320793030759027694741 339811912173316829423191)
                  ·
                    rfl

theorem cell22_2978016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 6].length) (baseStart_2978016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978016 prefixEnd_2978016 := by exact prefixLift 2978016
  have htrace : WordTrace (prefixWord ++ tailWord_2978016) baseStart_2978016 baseEnd_2978016 := by
    simpa [prefixWord, tailWord_2978016, baseEnd_2978016] using wordTrace_append hprefix tailTrace_2978016
  have hstable : (prefixWord ++ tailWord_2978016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978016).length < 2 ^ (prefixWord ++ tailWord_2978016).sum := by decide
  have hdescent : baseEnd_2978016 < baseStart_2978016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978082 : List Nat := [3, 3, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_2978082 : Nat := 118140960795 + 2978082 * 2 ^ 59
def prefixEnd_2978082 : Nat := 4983230072969 + 3 ^ 40 * 2978082 * 2
def baseEnd_2978082 : Nat := 1019458329668748316119371

theorem tailTrace_2978082 : CollatzResearch.WordTrace tailWord_2978082 prefixEnd_2978082 1019458329668748316119371 := by
  unfold tailWord_2978082
  simp only [CollatzResearch.WordTrace]
  refine ⟨27154893499231251189432125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72413049331283336505152333 27154893499231251189432125)
  ·
    refine ⟨10183085062211719196037047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27154893499231251189432125 10183085062211719196037047)
    ·
      refine ⟨15274627593317578794055571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10183085062211719196037047 15274627593317578794055571)
      ·
        refine ⟨22911941389976368191083357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15274627593317578794055571 22911941389976368191083357)
        ·
          refine ⟨8591978021241138071656259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22911941389976368191083357 8591978021241138071656259)
          ·
            refine ⟨12887967031861707107484389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8591978021241138071656259 12887967031861707107484389)
            ·
              refine ⟨2416493818474070082653323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12887967031861707107484389 2416493818474070082653323)
              ·
                refine ⟨3624740727711105123979985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2416493818474070082653323 3624740727711105123979985)
                ·
                  refine ⟨2718555545783328842984989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3624740727711105123979985 2718555545783328842984989)
                  ·
                    refine ⟨1019458329668748316119371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2718555545783328842984989 1019458329668748316119371)
                    ·
                      rfl

theorem cell22_2978082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_2978082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978082 prefixEnd_2978082 := by exact prefixLift 2978082
  have htrace : WordTrace (prefixWord ++ tailWord_2978082) baseStart_2978082 baseEnd_2978082 := by
    simpa [prefixWord, tailWord_2978082, baseEnd_2978082] using wordTrace_append hprefix tailTrace_2978082
  have hstable : (prefixWord ++ tailWord_2978082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978082).length < 2 ^ (prefixWord ++ tailWord_2978082).sum := by decide
  have hdescent : baseEnd_2978082 < baseStart_2978082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978121 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 2, 5]
def baseStart_2978121 : Nat := 118140960795 + 2978121 * 2 ^ 59
def prefixEnd_2978121 : Nat := 4983230072969 + 3 ^ 40 * 2978121 * 2
def baseEnd_2978121 : Nat := 1019471680165765214394251

theorem tailTrace_2978121 : CollatzResearch.WordTrace tailWord_2978121 prefixEnd_2978121 1019471680165765214394251 := by
  unfold tailWord_2978121
  simp only [CollatzResearch.WordTrace]
  refine ⟨108620996443783714418398217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72413997629189142945598811 108620996443783714418398217)
  ·
    refine ⟨81465747332837785813798663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108620996443783714418398217 81465747332837785813798663)
    ·
      refine ⟨122198620999256678720697995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81465747332837785813798663 122198620999256678720697995)
      ·
        refine ⟨183297931498885018081046993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122198620999256678720697995 183297931498885018081046993)
        ·
          refine ⟨137473448624163763560785245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183297931498885018081046993 137473448624163763560785245)
          ·
            refine ⟨51552543234061411335294467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137473448624163763560785245 51552543234061411335294467)
            ·
              refine ⟨77328814851092117002941701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51552543234061411335294467 77328814851092117002941701)
              ·
                refine ⟨14499152784579771938051569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77328814851092117002941701 14499152784579771938051569)
                ·
                  refine ⟨10874364588434828953538677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14499152784579771938051569 10874364588434828953538677)
                  ·
                    refine ⟨1019471680165765214394251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10874364588434828953538677 1019471680165765214394251)
                    ·
                      rfl

theorem cell22_2978121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_2978121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978121 prefixEnd_2978121 := by exact prefixLift 2978121
  have htrace : WordTrace (prefixWord ++ tailWord_2978121) baseStart_2978121 baseEnd_2978121 := by
    simpa [prefixWord, tailWord_2978121, baseEnd_2978121] using wordTrace_append hprefix tailTrace_2978121
  have hstable : (prefixWord ++ tailWord_2978121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978121).length < 2 ^ (prefixWord ++ tailWord_2978121).sum := by decide
  have hdescent : baseEnd_2978121 < baseStart_2978121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978153 : List Nat := [1, 2, 1, 1, 1, 3, 4, 4, 1, 4]
def baseStart_2978153 : Nat := 118140960795 + 2978153 * 2 ^ 59
def prefixEnd_2978153 : Nat := 4983230072969 + 3 ^ 40 * 2978153 * 2
def baseEnd_2978153 : Nat := 1019482634419727797594153

theorem tailTrace_2978153 : CollatzResearch.WordTrace tailWord_2978153 prefixEnd_2978153 1019482634419727797594153 := by
  unfold tailWord_2978153
  simp only [CollatzResearch.WordTrace]
  refine ⟨108622163579667783883563113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72414775719778522589042075 108622163579667783883563113)
  ·
    refine ⟨81466622684750837912672335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108622163579667783883563113 81466622684750837912672335)
    ·
      refine ⟨122199934027126256869008503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81466622684750837912672335 122199934027126256869008503)
      ·
        refine ⟨183299901040689385303512755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122199934027126256869008503 183299901040689385303512755)
        ·
          refine ⟨274949851561034077955269133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183299901040689385303512755 274949851561034077955269133)
          ·
            refine ⟨103106194335387779233225925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 274949851561034077955269133 103106194335387779233225925)
            ·
              refine ⟨19332411437885208606229861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103106194335387779233225925 19332411437885208606229861)
              ·
                refine ⟨3624827144603476613668099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19332411437885208606229861 3624827144603476613668099)
                ·
                  refine ⟨5437240716905214920502149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3624827144603476613668099 5437240716905214920502149)
                  ·
                    refine ⟨1019482634419727797594153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5437240716905214920502149 1019482634419727797594153)
                    ·
                      rfl

theorem cell22_2978153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 4].length) (baseStart_2978153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978153 prefixEnd_2978153 := by exact prefixLift 2978153
  have htrace : WordTrace (prefixWord ++ tailWord_2978153) baseStart_2978153 baseEnd_2978153 := by
    simpa [prefixWord, tailWord_2978153, baseEnd_2978153] using wordTrace_append hprefix tailTrace_2978153
  have hstable : (prefixWord ++ tailWord_2978153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978153).length < 2 ^ (prefixWord ++ tailWord_2978153).sum := by decide
  have hdescent : baseEnd_2978153 < baseStart_2978153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978185 : List Nat := [1, 2, 1, 1, 6, 1, 2, 4, 4]
def baseStart_2978185 : Nat := 118140960795 + 2978185 * 2 ^ 59
def prefixEnd_2978185 : Nat := 4983230072969 + 3 ^ 40 * 2978185 * 2
def baseEnd_2978185 : Nat := 339831196224563460264685

theorem tailTrace_2978185 : CollatzResearch.WordTrace tailWord_2978185 prefixEnd_2978185 339831196224563460264685 := by
  unfold tailWord_2978185
  simp only [CollatzResearch.WordTrace]
  refine ⟨108623330715551853348728009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72415553810367902232485339 108623330715551853348728009)
  ·
    refine ⟨81467498036663890011546007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108623330715551853348728009 81467498036663890011546007)
    ·
      refine ⟨122201247054995835017319011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81467498036663890011546007 122201247054995835017319011)
      ·
        refine ⟨183301870582493752525978517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122201247054995835017319011 183301870582493752525978517)
        ·
          refine ⟨8592275183554394649655243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 183301870582493752525978517 8592275183554394649655243)
          ·
            refine ⟨12888412775331591974482865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8592275183554394649655243 12888412775331591974482865)
            ·
              refine ⟨9666309581498693980862149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12888412775331591974482865 9666309581498693980862149)
              ·
                refine ⟨1812433046531005121411653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9666309581498693980862149 1812433046531005121411653)
                ·
                  refine ⟨339831196224563460264685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1812433046531005121411653 339831196224563460264685)
                  ·
                    rfl

theorem cell22_2978185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 4].length) (baseStart_2978185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978185 prefixEnd_2978185 := by exact prefixLift 2978185
  have htrace : WordTrace (prefixWord ++ tailWord_2978185) baseStart_2978185 baseEnd_2978185 := by
    simpa [prefixWord, tailWord_2978185, baseEnd_2978185] using wordTrace_append hprefix tailTrace_2978185
  have hstable : (prefixWord ++ tailWord_2978185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978185).length < 2 ^ (prefixWord ++ tailWord_2978185).sum := by decide
  have hdescent : baseEnd_2978185 < baseStart_2978185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978200 : List Nat := [2, 1, 2, 5, 1, 1, 3, 1, 1, 5]
def baseStart_2978200 : Nat := 118140960795 + 2978200 * 2 ^ 59
def prefixEnd_2978200 : Nat := 4983230072969 + 3 ^ 40 * 2978200 * 2
def baseEnd_2978200 : Nat := 1019498723480235341669009

theorem tailTrace_2978200 : CollatzResearch.WordTrace tailWord_2978200 prefixEnd_2978200 1019498723480235341669009 := by
  unfold tailWord_2978200
  simp only [CollatzResearch.WordTrace]
  refine ⟨54311938905248755455262027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72415918540331673940349369 54311938905248755455262027)
  ·
    refine ⟨81467908357873133182893041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54311938905248755455262027 81467908357873133182893041)
    ·
      refine ⟨61100931268404849887169781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81467908357873133182893041 61100931268404849887169781)
      ·
        refine ⟨5728212306412954676922167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61100931268404849887169781 5728212306412954676922167)
        ·
          refine ⟨8592318459619432015383251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5728212306412954676922167 8592318459619432015383251)
          ·
            refine ⟨12888477689429148023074877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8592318459619432015383251 12888477689429148023074877)
            ·
              refine ⟨4833179133535930508653079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12888477689429148023074877 4833179133535930508653079)
              ·
                refine ⟨7249768700303895762979619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4833179133535930508653079 7249768700303895762979619)
                ·
                  refine ⟨10874653050455843644469429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7249768700303895762979619 10874653050455843644469429)
                  ·
                    refine ⟨1019498723480235341669009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10874653050455843644469429 1019498723480235341669009)
                    ·
                      rfl

theorem cell22_2978200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_2978200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978200 prefixEnd_2978200 := by exact prefixLift 2978200
  have htrace : WordTrace (prefixWord ++ tailWord_2978200) baseStart_2978200 baseEnd_2978200 := by
    simpa [prefixWord, tailWord_2978200, baseEnd_2978200] using wordTrace_append hprefix tailTrace_2978200
  have hstable : (prefixWord ++ tailWord_2978200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978200).length < 2 ^ (prefixWord ++ tailWord_2978200).sum := by decide
  have hdescent : baseEnd_2978200 < baseStart_2978200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978262 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_2978262 : Nat := 118140960795 + 2978262 * 2 ^ 59
def prefixEnd_2978262 : Nat := 4983230072969 + 3 ^ 40 * 2978262 * 2
def baseEnd_2978262 : Nat := 1019519947347287846618819

theorem tailTrace_2978262 : CollatzResearch.WordTrace tailWord_2978262 prefixEnd_2978262 1019519947347287846618819 := by
  unfold tailWord_2978262
  simp only [CollatzResearch.WordTrace]
  refine ⟨6789133696017055968705065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72417426090848596999520693 6789133696017055968705065)
  ·
    refine ⟨5091850272012791976528799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6789133696017055968705065 5091850272012791976528799)
    ·
      refine ⟨7637775408019187964793199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5091850272012791976528799 7637775408019187964793199)
      ·
        refine ⟨11456663112028781947189799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7637775408019187964793199 11456663112028781947189799)
        ·
          refine ⟨17184994668043172920784699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11456663112028781947189799 17184994668043172920784699)
          ·
            refine ⟨25777492002064759381177049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17184994668043172920784699 25777492002064759381177049)
            ·
              refine ⟨19333119001548569535882787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25777492002064759381177049 19333119001548569535882787)
              ·
                refine ⟨28999678502322854303824181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19333119001548569535882787 28999678502322854303824181)
                ·
                  refine ⟨2718719859592767590983517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28999678502322854303824181 2718719859592767590983517)
                  ·
                    refine ⟨1019519947347287846618819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2718719859592767590983517 1019519947347287846618819)
                    ·
                      rfl

theorem cell22_2978262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_2978262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978262 prefixEnd_2978262 := by exact prefixLift 2978262
  have htrace : WordTrace (prefixWord ++ tailWord_2978262) baseStart_2978262 baseEnd_2978262 := by
    simpa [prefixWord, tailWord_2978262, baseEnd_2978262] using wordTrace_append hprefix tailTrace_2978262
  have hstable : (prefixWord ++ tailWord_2978262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978262).length < 2 ^ (prefixWord ++ tailWord_2978262).sum := by decide
  have hdescent : baseEnd_2978262 < baseStart_2978262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978303 : List Nat := [1, 1, 2, 2, 1, 2, 4, 3, 6]
def baseStart_2978303 : Nat := 118140960795 + 2978303 * 2 ^ 59
def prefixEnd_2978303 : Nat := 4983230072969 + 3 ^ 40 * 2978303 * 2
def baseEnd_2978303 : Nat := 339844660828392468781231

theorem tailTrace_2978303 : CollatzResearch.WordTrace tailWord_2978303 prefixEnd_2978303 339844660828392468781231 := by
  unfold tailWord_2978303
  simp only [CollatzResearch.WordTrace]
  refine ⟨108627634529124359501523563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72418423019416239667682375 108627634529124359501523563)
  ·
    refine ⟨162941451793686539252285345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108627634529124359501523563 162941451793686539252285345)
    ·
      refine ⟨122206088845264904439214009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162941451793686539252285345 122206088845264904439214009)
      ·
        refine ⟨91654566633948678329410507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122206088845264904439214009 91654566633948678329410507)
        ·
          refine ⟨137481849950923017494115761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91654566633948678329410507 137481849950923017494115761)
          ·
            refine ⟨103111387463192263120586821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137481849950923017494115761 103111387463192263120586821)
            ·
              refine ⟨19333385149348549335110029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103111387463192263120586821 19333385149348549335110029)
              ·
                refine ⟨7250019431005706000666261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19333385149348549335110029 7250019431005706000666261)
                ·
                  refine ⟨339844660828392468781231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7250019431005706000666261 339844660828392468781231)
                  ·
                    rfl

theorem cell22_2978303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 6].length) (baseStart_2978303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978303 prefixEnd_2978303 := by exact prefixLift 2978303
  have htrace : WordTrace (prefixWord ++ tailWord_2978303) baseStart_2978303 baseEnd_2978303 := by
    simpa [prefixWord, tailWord_2978303, baseEnd_2978303] using wordTrace_append hprefix tailTrace_2978303
  have hstable : (prefixWord ++ tailWord_2978303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978303).length < 2 ^ (prefixWord ++ tailWord_2978303).sum := by decide
  have hdescent : baseEnd_2978303 < baseStart_2978303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978305 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 3, 4]
def baseStart_2978305 : Nat := 118140960795 + 2978305 * 2 ^ 59
def prefixEnd_2978305 : Nat := 4983230072969 + 3 ^ 40 * 2978305 * 2
def baseEnd_2978305 : Nat := 1019534667126050067793687

theorem tailTrace_2978305 : CollatzResearch.WordTrace tailWord_2978305 prefixEnd_2978305 1019534667126050067793687 := by
  unfold tailWord_2978305
  simp only [CollatzResearch.WordTrace]
  refine ⟨108627707475117113843096369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72418471650078075895397579 108627707475117113843096369)
  ·
    refine ⟨81470780606337835382322277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108627707475117113843096369 81470780606337835382322277)
    ·
      refine ⟨15275771363688344134185427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81470780606337835382322277 15275771363688344134185427)
      ·
        refine ⟨22913657045532516201278141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15275771363688344134185427 22913657045532516201278141)
        ·
          refine ⟨8592621392074693575479303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22913657045532516201278141 8592621392074693575479303)
          ·
            refine ⟨12888932088112040363218955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8592621392074693575479303 12888932088112040363218955)
            ·
              refine ⟨19333398132168060544828433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12888932088112040363218955 19333398132168060544828433)
              ·
                refine ⟨14500048599126045408621325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19333398132168060544828433 14500048599126045408621325)
                ·
                  refine ⟨5437518224672267028232997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14500048599126045408621325 5437518224672267028232997)
                  ·
                    refine ⟨1019534667126050067793687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5437518224672267028232997 1019534667126050067793687)
                    ·
                      rfl

theorem cell22_2978305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_2978305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978305 prefixEnd_2978305 := by exact prefixLift 2978305
  have htrace : WordTrace (prefixWord ++ tailWord_2978305) baseStart_2978305 baseEnd_2978305 := by
    simpa [prefixWord, tailWord_2978305, baseEnd_2978305] using wordTrace_append hprefix tailTrace_2978305
  have hstable : (prefixWord ++ tailWord_2978305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978305).length < 2 ^ (prefixWord ++ tailWord_2978305).sum := by decide
  have hdescent : baseEnd_2978305 < baseStart_2978305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978335 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 4, 3]
def baseStart_2978335 : Nat := 118140960795 + 2978335 * 2 ^ 59
def prefixEnd_2978335 : Nat := 4983230072969 + 3 ^ 40 * 2978335 * 2
def baseEnd_2978335 : Nat := 1019544936739139989543595

theorem tailTrace_2978335 : CollatzResearch.WordTrace tailWord_2978335 prefixEnd_2978335 1019544936739139989543595 := by
  unfold tailWord_2978335
  simp only [CollatzResearch.WordTrace]
  refine ⟨108628801665008428966688459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72419201110005619311125639 108628801665008428966688459)
  ·
    refine ⟨162943202497512643450032689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108628801665008428966688459 162943202497512643450032689)
    ·
      refine ⟨122207401873134482587524517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162943202497512643450032689 122207401873134482587524517)
      ·
        refine ⟨22913887851212715485160847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122207401873134482587524517 22913887851212715485160847)
        ·
          refine ⟨34370831776819073227741271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22913887851212715485160847 34370831776819073227741271)
          ·
            refine ⟨51556247665228609841611907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34370831776819073227741271 51556247665228609841611907)
            ·
              refine ⟨77334371497842914762417861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51556247665228609841611907 77334371497842914762417861)
              ·
                refine ⟨14500194655845546517953349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77334371497842914762417861 14500194655845546517953349)
                ·
                  refine ⟨2718786497971039972116253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14500194655845546517953349 2718786497971039972116253)
                  ·
                    refine ⟨1019544936739139989543595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2718786497971039972116253 1019544936739139989543595)
                    ·
                      rfl

theorem cell22_2978335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 3].length) (baseStart_2978335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978335 prefixEnd_2978335 := by exact prefixLift 2978335
  have htrace : WordTrace (prefixWord ++ tailWord_2978335) baseStart_2978335 baseEnd_2978335 := by
    simpa [prefixWord, tailWord_2978335, baseEnd_2978335] using wordTrace_append hprefix tailTrace_2978335
  have hstable : (prefixWord ++ tailWord_2978335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978335).length < 2 ^ (prefixWord ++ tailWord_2978335).sum := by decide
  have hdescent : baseEnd_2978335 < baseStart_2978335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978337 : List Nat := [1, 2, 3, 2, 2, 1, 4, 3, 4]
def baseStart_2978337 : Nat := 118140960795 + 2978337 * 2 ^ 59
def prefixEnd_2978337 : Nat := 4983230072969 + 3 ^ 40 * 2978337 * 2
def baseEnd_2978337 : Nat := 339848540460004216997863

theorem tailTrace_2978337 : CollatzResearch.WordTrace tailWord_2978337 prefixEnd_2978337 339848540460004216997863 := by
  unfold tailWord_2978337
  simp only [CollatzResearch.WordTrace]
  refine ⟨108628874611001183308261265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72419249740667455538840843 108628874611001183308261265)
  ·
    refine ⟨81471655958250887481195949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108628874611001183308261265 81471655958250887481195949)
    ·
      refine ⟨30551870984344082805448481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81471655958250887481195949 30551870984344082805448481)
      ·
        refine ⟨22913903238258062104086361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30551870984344082805448481 22913903238258062104086361)
        ·
          refine ⟨17185427428693546578064771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22913903238258062104086361 17185427428693546578064771)
          ·
            refine ⟨25778141143040319867097157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17185427428693546578064771 25778141143040319867097157)
            ·
              refine ⟨4833401464320059975080717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25778141143040319867097157 4833401464320059975080717)
              ·
                refine ⟨1812525549120022490655269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4833401464320059975080717 1812525549120022490655269)
                ·
                  refine ⟨339848540460004216997863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1812525549120022490655269 339848540460004216997863)
                  ·
                    rfl

theorem cell22_2978337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 4].length) (baseStart_2978337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978337 prefixEnd_2978337 := by exact prefixLift 2978337
  have htrace : WordTrace (prefixWord ++ tailWord_2978337) baseStart_2978337 baseEnd_2978337 := by
    simpa [prefixWord, tailWord_2978337, baseEnd_2978337] using wordTrace_append hprefix tailTrace_2978337
  have hstable : (prefixWord ++ tailWord_2978337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978337).length < 2 ^ (prefixWord ++ tailWord_2978337).sum := by decide
  have hdescent : baseEnd_2978337 < baseStart_2978337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978339 : List Nat := [1, 1, 1, 4, 4, 3, 2, 1, 1, 4]
def baseStart_2978339 : Nat := 118140960795 + 2978339 * 2 ^ 59
def prefixEnd_2978339 : Nat := 4983230072969 + 3 ^ 40 * 2978339 * 2
def baseEnd_2978339 : Nat := 1019546306020885312443583

theorem tailTrace_2978339 : CollatzResearch.WordTrace tailWord_2978339 prefixEnd_2978339 1019546306020885312443583 := by
  unfold tailWord_2978339
  simp only [CollatzResearch.WordTrace]
  refine ⟨108628947556993937649834071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72419298371329291766556047 108628947556993937649834071)
  ·
    refine ⟨162943421335490906474751107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108628947556993937649834071 162943421335490906474751107)
    ·
      refine ⟨244415132003236359712126661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162943421335490906474751107 244415132003236359712126661)
      ·
        refine ⟨45827837250606817446023749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244415132003236359712126661 45827837250606817446023749)
        ·
          refine ⟨8592719484488778271129453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45827837250606817446023749 8592719484488778271129453)
          ·
            refine ⟨3222269806683291851673545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8592719484488778271129453 3222269806683291851673545)
            ·
              refine ⟨2416702355012468888755159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3222269806683291851673545 2416702355012468888755159)
              ·
                refine ⟨3625053532518703333132739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2416702355012468888755159 3625053532518703333132739)
                ·
                  refine ⟨5437580298778054999699109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3625053532518703333132739 5437580298778054999699109)
                  ·
                    refine ⟨1019546306020885312443583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5437580298778054999699109 1019546306020885312443583)
                    ·
                      rfl

theorem cell22_2978339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 1, 4].length) (baseStart_2978339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978339 prefixEnd_2978339 := by exact prefixLift 2978339
  have htrace : WordTrace (prefixWord ++ tailWord_2978339) baseStart_2978339 baseEnd_2978339 := by
    simpa [prefixWord, tailWord_2978339, baseEnd_2978339] using wordTrace_append hprefix tailTrace_2978339
  have hstable : (prefixWord ++ tailWord_2978339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978339).length < 2 ^ (prefixWord ++ tailWord_2978339).sum := by decide
  have hdescent : baseEnd_2978339 < baseStart_2978339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978352 : List Nat := [2, 1, 1, 1, 2, 3, 5, 2, 2, 3]
def baseStart_2978352 : Nat := 118140960795 + 2978352 * 2 ^ 59
def prefixEnd_2978352 : Nat := 4983230072969 + 3 ^ 40 * 2978352 * 2
def baseEnd_2978352 : Nat := 1019550756186557611868543

theorem tailTrace_2978352 : CollatzResearch.WordTrace tailWord_2978352 prefixEnd_2978352 1019550756186557611868543 := by
  unfold tailWord_2978352
  simp only [CollatzResearch.WordTrace]
  refine ⟨54314710852973420435028655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72419614470631227246704873 54314710852973420435028655)
  ·
    refine ⟨81472066279460130652542983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54314710852973420435028655 81472066279460130652542983)
    ·
      refine ⟨122208099419190195978814475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81472066279460130652542983 122208099419190195978814475)
      ·
        refine ⟨183312149128785293968221713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122208099419190195978814475 183312149128785293968221713)
        ·
          refine ⟨137484111846588970476166285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183312149128785293968221713 137484111846588970476166285)
          ·
            refine ⟨51556541942470863928562357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137484111846588970476166285 51556541942470863928562357)
            ·
              refine ⟨4833425807106643493302721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51556541942470863928562357 4833425807106643493302721)
              ·
                refine ⟨3625069355329982619977041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4833425807106643493302721 3625069355329982619977041)
                ·
                  refine ⟨2718802016497486964982781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3625069355329982619977041 2718802016497486964982781)
                  ·
                    refine ⟨1019550756186557611868543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2718802016497486964982781 1019550756186557611868543)
                    ·
                      rfl

theorem cell22_2978352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 2, 3].length) (baseStart_2978352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978352 prefixEnd_2978352 := by exact prefixLift 2978352
  have htrace : WordTrace (prefixWord ++ tailWord_2978352) baseStart_2978352 baseEnd_2978352 := by
    simpa [prefixWord, tailWord_2978352, baseEnd_2978352] using wordTrace_append hprefix tailTrace_2978352
  have hstable : (prefixWord ++ tailWord_2978352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978352).length < 2 ^ (prefixWord ++ tailWord_2978352).sum := by decide
  have hdescent : baseEnd_2978352 < baseStart_2978352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978410 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 7]
def baseStart_2978410 : Nat := 118140960795 + 2978410 * 2 ^ 59
def prefixEnd_2978410 : Nat := 4983230072969 + 3 ^ 40 * 2978410 * 2
def baseEnd_2978410 : Nat := 339856870257288264639455

theorem tailTrace_2978410 : CollatzResearch.WordTrace tailWord_2978410 prefixEnd_2978410 339856870257288264639455 := by
  unfold tailWord_2978410
  simp only [CollatzResearch.WordTrace]
  refine ⟨27157884284934179193917171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72421024759824477850445789 27157884284934179193917171)
  ·
    refine ⟨40736826427401268790875757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27157884284934179193917171 40736826427401268790875757)
    ·
      refine ⟨15276309910275475796578409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40736826427401268790875757 15276309910275475796578409)
      ·
        refine ⟨11457232432706606847433807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15276309910275475796578409 11457232432706606847433807)
        ·
          refine ⟨17185848649059910271150711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11457232432706606847433807 17185848649059910271150711)
          ·
            refine ⟨25778772973589865406726067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17185848649059910271150711 25778772973589865406726067)
            ·
              refine ⟨38668159460384798110089101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25778772973589865406726067 38668159460384798110089101)
              ·
                refine ⟨14500559797644299291283413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38668159460384798110089101 14500559797644299291283413)
                ·
                  refine ⟨339856870257288264639455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14500559797644299291283413 339856870257288264639455)
                  ·
                    rfl

theorem cell22_2978410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_2978410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978410 prefixEnd_2978410 := by exact prefixLift 2978410
  have htrace : WordTrace (prefixWord ++ tailWord_2978410) baseStart_2978410 baseEnd_2978410 := by
    simpa [prefixWord, tailWord_2978410, baseEnd_2978410] using wordTrace_append hprefix tailTrace_2978410
  have hstable : (prefixWord ++ tailWord_2978410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978410).length < 2 ^ (prefixWord ++ tailWord_2978410).sum := by decide
  have hdescent : baseEnd_2978410 < baseStart_2978410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978414 : List Nat := [4, 1, 2, 2, 2, 1, 3, 1, 3, 3]
def baseStart_2978414 : Nat := 118140960795 + 2978414 * 2 ^ 59
def prefixEnd_2978414 : Nat := 4983230072969 + 3 ^ 40 * 2978414 * 2
def baseEnd_2978414 : Nat := 1019571980053610116818353

theorem tailTrace_2978414 : CollatzResearch.WordTrace tailWord_2978414 prefixEnd_2978414 1019571980053610116818353 := by
  unfold tailWord_2978414
  simp only [CollatzResearch.WordTrace]
  refine ⟨13578960378965278182351787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72421122021148150305876197 13578960378965278182351787)
  ·
    refine ⟨20368440568447917273527681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13578960378965278182351787 20368440568447917273527681)
    ·
      refine ⟨15276330426335937955145761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20368440568447917273527681 15276330426335937955145761)
      ·
        refine ⟨11457247819751953466359321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15276330426335937955145761 11457247819751953466359321)
        ·
          refine ⟨8592935864813965099769491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11457247819751953466359321 8592935864813965099769491)
          ·
            refine ⟨12889403797220947649654237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8592935864813965099769491 12889403797220947649654237)
            ·
              refine ⟨4833526423957855368620339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12889403797220947649654237 4833526423957855368620339)
              ·
                refine ⟨7250289635936783052930509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4833526423957855368620339 7250289635936783052930509)
                ·
                  refine ⟨2718858613476293644848941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7250289635936783052930509 2718858613476293644848941)
                  ·
                    refine ⟨1019571980053610116818353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2718858613476293644848941 1019571980053610116818353)
                    ·
                      rfl

theorem cell22_2978414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_2978414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978414 prefixEnd_2978414 := by exact prefixLift 2978414
  have htrace : WordTrace (prefixWord ++ tailWord_2978414) baseStart_2978414 baseEnd_2978414 := by
    simpa [prefixWord, tailWord_2978414, baseEnd_2978414] using wordTrace_append hprefix tailTrace_2978414
  have hstable : (prefixWord ++ tailWord_2978414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978414).length < 2 ^ (prefixWord ++ tailWord_2978414).sum := by decide
  have hdescent : baseEnd_2978414 < baseStart_2978414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978465 : List Nat := [1, 2, 3, 3, 4, 1, 2, 2, 1, 3]
def baseStart_2978465 : Nat := 118140960795 + 2978465 * 2 ^ 59
def prefixEnd_2978465 : Nat := 4983230072969 + 3 ^ 40 * 2978465 * 2
def baseEnd_2978465 : Nat := 1019589438395862983793197

theorem tailTrace_2978465 : CollatzResearch.WordTrace tailWord_2978465 prefixEnd_2978465 1019589438395862983793197 := by
  unfold tailWord_2978465
  simp only [CollatzResearch.WordTrace]
  refine ⟨108633543154537461168920849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72422362103024974112613899 108633543154537461168920849)
  ·
    refine ⟨81475157365903095876690637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108633543154537461168920849 81475157365903095876690637)
    ·
      refine ⟨30553184012213660953758989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81475157365903095876690637 30553184012213660953758989)
      ·
        refine ⟨11457444004580122857659621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30553184012213660953758989 11457444004580122857659621)
        ·
          refine ⟨2148270750858773035811179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11457444004580122857659621 2148270750858773035811179)
          ·
            refine ⟨3222406126288159553716769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2148270750858773035811179 3222406126288159553716769)
            ·
              refine ⟨2416804594716119665287577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3222406126288159553716769 2416804594716119665287577)
              ·
                refine ⟨1812603446037089748965683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2416804594716119665287577 1812603446037089748965683)
                ·
                  refine ⟨2718905169055634623448525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1812603446037089748965683 2718905169055634623448525)
                  ·
                    refine ⟨1019589438395862983793197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2718905169055634623448525 1019589438395862983793197)
                    ·
                      rfl

theorem cell22_2978465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_2978465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978465 prefixEnd_2978465 := by exact prefixLift 2978465
  have htrace : WordTrace (prefixWord ++ tailWord_2978465) baseStart_2978465 baseEnd_2978465 := by
    simpa [prefixWord, tailWord_2978465, baseEnd_2978465] using wordTrace_append hprefix tailTrace_2978465
  have hstable : (prefixWord ++ tailWord_2978465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978465).length < 2 ^ (prefixWord ++ tailWord_2978465).sum := by decide
  have hdescent : baseEnd_2978465 < baseStart_2978465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978583 : List Nat := [1, 1, 3, 4, 4, 1, 1, 1, 3, 3]
def baseStart_2978583 : Nat := 118140960795 + 2978583 * 2 ^ 59
def prefixEnd_2978583 : Nat := 4983230072969 + 3 ^ 40 * 2978583 * 2
def baseEnd_2978583 : Nat := 1019629832207350009342835

theorem tailTrace_2978583 : CollatzResearch.WordTrace tailWord_2978583 prefixEnd_2978583 1019629832207350009342835 := by
  unfold tailWord_2978583
  simp only [CollatzResearch.WordTrace]
  refine ⟨108637846968109967321716403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72425231312073311547810935 108637846968109967321716403)
  ·
    refine ⟨162956770452164950982574605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108637846968109967321716403 162956770452164950982574605)
    ·
      refine ⟨61108788919561856618465477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162956770452164950982574605 61108788919561856618465477)
      ·
        refine ⟨11457897922417848115962277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61108788919561856618465477 11457897922417848115962277)
        ·
          refine ⟨2148355860453346521742927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11457897922417848115962277 2148355860453346521742927)
          ·
            refine ⟨3222533790680019782614391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2148355860453346521742927 3222533790680019782614391)
            ·
              refine ⟨4833800686020029673921587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3222533790680019782614391 4833800686020029673921587)
              ·
                refine ⟨7250701029030044510882381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4833800686020029673921587 7250701029030044510882381)
                ·
                  refine ⟨2719012885886266691580893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7250701029030044510882381 2719012885886266691580893)
                  ·
                    refine ⟨1019629832207350009342835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2719012885886266691580893 1019629832207350009342835)
                    ·
                      rfl

theorem cell22_2978583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 3, 3].length) (baseStart_2978583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978583 prefixEnd_2978583 := by exact prefixLift 2978583
  have htrace : WordTrace (prefixWord ++ tailWord_2978583) baseStart_2978583 baseEnd_2978583 := by
    simpa [prefixWord, tailWord_2978583, baseEnd_2978583] using wordTrace_append hprefix tailTrace_2978583
  have hstable : (prefixWord ++ tailWord_2978583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978583).length < 2 ^ (prefixWord ++ tailWord_2978583).sum := by decide
  have hdescent : baseEnd_2978583 < baseStart_2978583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978641 : List Nat := [1, 2, 2, 1, 6, 1, 1, 4, 4]
def baseStart_2978641 : Nat := 118140960795 + 2978641 * 2 ^ 59
def prefixEnd_2978641 : Nat := 4983230072969 + 3 ^ 40 * 2978641 * 2
def baseEnd_2978641 : Nat := 339883228930885730464219

theorem tailTrace_2978641 : CollatzResearch.WordTrace tailWord_2978641 prefixEnd_2978641 339883228930885730464219 := by
  unfold tailWord_2978641
  simp only [CollatzResearch.WordTrace]
  refine ⟨108639962401899843227327777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72426641601266562151551851 108639962401899843227327777)
  ·
    refine ⟨81479971801424882420495833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108639962401899843227327777 81479971801424882420495833)
    ·
      refine ⟨61109978851068661815371875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81479971801424882420495833 61109978851068661815371875)
      ·
        refine ⟨91664968276602992723057813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61109978851068661815371875 91664968276602992723057813)
        ·
          refine ⟨4296795387965765283893335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91664968276602992723057813 4296795387965765283893335)
          ·
            refine ⟨6445193081948647925840003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4296795387965765283893335 6445193081948647925840003)
            ·
              refine ⟨9667789622922971888760005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6445193081948647925840003 9667789622922971888760005)
              ·
                refine ⟨1812710554298057229142501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9667789622922971888760005 1812710554298057229142501)
                ·
                  refine ⟨339883228930885730464219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1812710554298057229142501 339883228930885730464219)
                  ·
                    rfl

theorem cell22_2978641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 4].length) (baseStart_2978641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978641 prefixEnd_2978641 := by exact prefixLift 2978641
  have htrace : WordTrace (prefixWord ++ tailWord_2978641) baseStart_2978641 baseEnd_2978641 := by
    simpa [prefixWord, tailWord_2978641, baseEnd_2978641] using wordTrace_append hprefix tailTrace_2978641
  have hstable : (prefixWord ++ tailWord_2978641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978641).length < 2 ^ (prefixWord ++ tailWord_2978641).sum := by decide
  have hdescent : baseEnd_2978641 < baseStart_2978641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978686 : List Nat := [4, 2, 3, 1, 2, 1, 9]
def baseStart_2978686 : Nat := 118140960795 + 2978686 * 2 ^ 59
def prefixEnd_2978686 : Nat := 4983230072969 + 3 ^ 40 * 2978686 * 2
def baseEnd_2978686 : Nat := 37765373748603410148797

theorem tailTrace_2978686 : CollatzResearch.WordTrace tailWord_2978686 prefixEnd_2978686 37765373748603410148797 := by
  unfold tailWord_2978686
  simp only [CollatzResearch.WordTrace]
  refine ⟨13580200460842101989089489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72427735791157877275143941 13580200460842101989089489)
  ·
    refine ⟨10185150345631576491817117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13580200460842101989089489 10185150345631576491817117)
    ·
      refine ⟨3819431379611841184431419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10185150345631576491817117 3819431379611841184431419)
      ·
        refine ⟨5729147069417761776647129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3819431379611841184431419 5729147069417761776647129)
        ·
          refine ⟨4296860302063321332485347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5729147069417761776647129 4296860302063321332485347)
          ·
            refine ⟨6445290453094981998728021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4296860302063321332485347 6445290453094981998728021)
            ·
              refine ⟨37765373748603410148797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6445290453094981998728021 37765373748603410148797)
              ·
                rfl

theorem cell22_2978686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 9].length) (baseStart_2978686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978686 prefixEnd_2978686 := by exact prefixLift 2978686
  have htrace : WordTrace (prefixWord ++ tailWord_2978686) baseStart_2978686 baseEnd_2978686 := by
    simpa [prefixWord, tailWord_2978686, baseEnd_2978686] using wordTrace_append hprefix tailTrace_2978686
  have hstable : (prefixWord ++ tailWord_2978686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978686).length < 2 ^ (prefixWord ++ tailWord_2978686).sum := by decide
  have hdescent : baseEnd_2978686 < baseStart_2978686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978690 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_2978690 : Nat := 118140960795 + 2978690 * 2 ^ 59
def prefixEnd_2978690 : Nat := 4983230072969 + 3 ^ 40 * 2978690 * 2
def baseEnd_2978690 : Nat := 1019666460494037396917507

theorem tailTrace_2978690 : CollatzResearch.WordTrace tailWord_2978690 prefixEnd_2978690 1019666460494037396917507 := by
  unfold tailWord_2978690
  simp only [CollatzResearch.WordTrace]
  refine ⟨27160437394680581148965381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72427833052481549730574349 27160437394680581148965381)
  ·
    refine ⟨5092582011502608965431009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27160437394680581148965381 5092582011502608965431009)
    ·
      refine ⟨3819436508626956724073257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5092582011502608965431009 3819436508626956724073257)
      ·
        refine ⟨2864577381470217543054943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3819436508626956724073257 2864577381470217543054943)
        ·
          refine ⟨4296866072205326314582415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2864577381470217543054943 4296866072205326314582415)
          ·
            refine ⟨6445299108307989471873623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4296866072205326314582415 6445299108307989471873623)
            ·
              refine ⟨9667948662461984207810435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6445299108307989471873623 9667948662461984207810435)
              ·
                refine ⟨14501922993692976311715653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9667948662461984207810435 14501922993692976311715653)
                ·
                  refine ⟨2719110561317433058446685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14501922993692976311715653 2719110561317433058446685)
                  ·
                    refine ⟨1019666460494037396917507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2719110561317433058446685 1019666460494037396917507)
                    ·
                      rfl

theorem cell22_2978690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_2978690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978690 prefixEnd_2978690 := by exact prefixLift 2978690
  have htrace : WordTrace (prefixWord ++ tailWord_2978690) baseStart_2978690 baseEnd_2978690 := by
    simpa [prefixWord, tailWord_2978690, baseEnd_2978690] using wordTrace_append hprefix tailTrace_2978690
  have hstable : (prefixWord ++ tailWord_2978690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978690).length < 2 ^ (prefixWord ++ tailWord_2978690).sum := by decide
  have hdescent : baseEnd_2978690 < baseStart_2978690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978758 : List Nat := [6, 1, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_2978758 : Nat := 118140960795 + 2978758 * 2 ^ 59
def prefixEnd_2978758 : Nat := 4983230072969 + 3 ^ 40 * 2978758 * 2
def baseEnd_2978758 : Nat := 1019689738283707886217299

theorem tailTrace_2978758 : CollatzResearch.WordTrace tailWord_2978758 prefixEnd_2978758 1019689738283707886217299 := by
  unfold tailWord_2978758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3395132179452374131541779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72429486494983981472891285 3395132179452374131541779)
  ·
    refine ⟨5092698269178561197312669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3395132179452374131541779 5092698269178561197312669)
    ·
      refine ⟨1909761850941960448992251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5092698269178561197312669 1909761850941960448992251)
      ·
        refine ⟨2864642776412940673488377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1909761850941960448992251 2864642776412940673488377)
        ·
          refine ⟨2148482082309705505116283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2864642776412940673488377 2148482082309705505116283)
          ·
            refine ⟨3222723123464558257674425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2148482082309705505116283 3222723123464558257674425)
            ·
              refine ⟨2417042342598418693255819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3222723123464558257674425 2417042342598418693255819)
              ·
                refine ⟨3625563513897628039883729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2417042342598418693255819 3625563513897628039883729)
                ·
                  refine ⟨2719172635423221029912797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3625563513897628039883729 2719172635423221029912797)
                  ·
                    refine ⟨1019689738283707886217299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2719172635423221029912797 1019689738283707886217299)
                    ·
                      rfl

theorem cell22_2978758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_2978758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978758 prefixEnd_2978758 := by exact prefixLift 2978758
  have htrace : WordTrace (prefixWord ++ tailWord_2978758) baseStart_2978758 baseEnd_2978758 := by
    simpa [prefixWord, tailWord_2978758, baseEnd_2978758] using wordTrace_append hprefix tailTrace_2978758
  have hstable : (prefixWord ++ tailWord_2978758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978758).length < 2 ^ (prefixWord ++ tailWord_2978758).sum := by decide
  have hdescent : baseEnd_2978758 < baseStart_2978758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978759 : List Nat := [1, 1, 4, 1, 1, 2, 5, 1, 6]
def baseStart_2978759 : Nat := 118140960795 + 2978759 * 2 ^ 59
def prefixEnd_2978759 : Nat := 4983230072969 + 3 ^ 40 * 2978759 * 2
def baseEnd_2978759 : Nat := 339896693534714738980765

theorem tailTrace_2978759 : CollatzResearch.WordTrace tailWord_2978759 prefixEnd_2978759 339896693534714738980765 := by
  unfold tailWord_2978759
  simp only [CollatzResearch.WordTrace]
  refine ⟨108644266215472349380123331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72429510810314899586748887 108644266215472349380123331)
  ·
    refine ⟨162966399323208524070184997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108644266215472349380123331 162966399323208524070184997)
    ·
      refine ⟨30556199873101598263159687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162966399323208524070184997 30556199873101598263159687)
      ·
        refine ⟨45834299809652397394739531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30556199873101598263159687 45834299809652397394739531)
        ·
          refine ⟨68751449714478596092109297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45834299809652397394739531 68751449714478596092109297)
          ·
            refine ⟨51563587285858947069081973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68751449714478596092109297 51563587285858947069081973)
            ·
              refine ⟨4834086308049276287726435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51563587285858947069081973 4834086308049276287726435)
              ·
                refine ⟨7251129462073914431589653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4834086308049276287726435 7251129462073914431589653)
                ·
                  refine ⟨339896693534714738980765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7251129462073914431589653 339896693534714738980765)
                  ·
                    rfl

theorem cell22_2978759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 6].length) (baseStart_2978759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978759 prefixEnd_2978759 := by exact prefixLift 2978759
  have htrace : WordTrace (prefixWord ++ tailWord_2978759) baseStart_2978759 baseEnd_2978759 := by
    simpa [prefixWord, tailWord_2978759, baseEnd_2978759] using wordTrace_append hprefix tailTrace_2978759
  have hstable : (prefixWord ++ tailWord_2978759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978759).length < 2 ^ (prefixWord ++ tailWord_2978759).sum := by decide
  have hdescent : baseEnd_2978759 < baseStart_2978759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978778 : List Nat := [3, 1, 1, 2, 4, 3, 1, 2, 1, 4]
def baseStart_2978778 : Nat := 118140960795 + 2978778 * 2 ^ 59
def prefixEnd_2978778 : Nat := 4983230072969 + 3 ^ 40 * 2978778 * 2
def baseEnd_2978778 : Nat := 1019696584692434500717237

theorem tailTrace_2978778 : CollatzResearch.WordTrace tailWord_2978778 prefixEnd_2978778 1019696584692434500717237 := by
  unfold tailWord_2978778
  simp only [CollatzResearch.WordTrace]
  refine ⟨27161239800600878906266247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72429972801602343750043325 27161239800600878906266247)
  ·
    refine ⟨40741859700901318359399371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27161239800600878906266247 40741859700901318359399371)
    ·
      refine ⟨61112789551351977539099057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40741859700901318359399371 61112789551351977539099057)
      ·
        refine ⟨45834592163513983154324293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61112789551351977539099057 45834592163513983154324293)
        ·
          refine ⟨8593986030658871841435805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45834592163513983154324293 8593986030658871841435805)
          ·
            refine ⟨3222744761497076940538427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8593986030658871841435805 3222744761497076940538427)
            ·
              refine ⟨4834117142245615410807641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3222744761497076940538427 4834117142245615410807641)
              ·
                refine ⟨3625587856684211558105731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4834117142245615410807641 3625587856684211558105731)
                ·
                  refine ⟨5438381785026317337158597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3625587856684211558105731 5438381785026317337158597)
                  ·
                    refine ⟨1019696584692434500717237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5438381785026317337158597 1019696584692434500717237)
                    ·
                      rfl

theorem cell22_2978778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_2978778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978778 prefixEnd_2978778 := by exact prefixLift 2978778
  have htrace : WordTrace (prefixWord ++ tailWord_2978778) baseStart_2978778 baseEnd_2978778 := by
    simpa [prefixWord, tailWord_2978778, baseEnd_2978778] using wordTrace_append hprefix tailTrace_2978778
  have hstable : (prefixWord ++ tailWord_2978778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978778).length < 2 ^ (prefixWord ++ tailWord_2978778).sum := by decide
  have hdescent : baseEnd_2978778 < baseStart_2978778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978791 : List Nat := [1, 1, 5, 2, 2, 2, 1, 2, 1, 5]
def baseStart_2978791 : Nat := 118140960795 + 2978791 * 2 ^ 59
def prefixEnd_2978791 : Nat := 4983230072969 + 3 ^ 40 * 2978791 * 2
def baseEnd_2978791 : Nat := 1019701034858106800142197

theorem tailTrace_2978791 : CollatzResearch.WordTrace tailWord_2978791 prefixEnd_2978791 1019701034858106800142197 := by
  unfold tailWord_2978791
  simp only [CollatzResearch.WordTrace]
  refine ⟨108645433351356418845288227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72430288900904279230192151 108645433351356418845288227)
  ·
    refine ⟨162968150027034628267932341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108645433351356418845288227 162968150027034628267932341)
    ·
      refine ⟨15278264065034496400118657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162968150027034628267932341 15278264065034496400118657)
      ·
        refine ⟨11458698048775872300088993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15278264065034496400118657 11458698048775872300088993)
        ·
          refine ⟨8594023536581904225066745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11458698048775872300088993 8594023536581904225066745)
          ·
            refine ⟨6445517652436428168800059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8594023536581904225066745 6445517652436428168800059)
            ·
              refine ⟨9668276478654642253200089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6445517652436428168800059 9668276478654642253200089)
              ·
                refine ⟨7251207358990981689900067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9668276478654642253200089 7251207358990981689900067)
                ·
                  refine ⟨10876811038486472534850101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7251207358990981689900067 10876811038486472534850101)
                  ·
                    refine ⟨1019701034858106800142197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10876811038486472534850101 1019701034858106800142197)
                    ·
                      rfl

theorem cell22_2978791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_2978791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978791 prefixEnd_2978791 := by exact prefixLift 2978791
  have htrace : WordTrace (prefixWord ++ tailWord_2978791) baseStart_2978791 baseEnd_2978791 := by
    simpa [prefixWord, tailWord_2978791, baseEnd_2978791] using wordTrace_append hprefix tailTrace_2978791
  have hstable : (prefixWord ++ tailWord_2978791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978791).length < 2 ^ (prefixWord ++ tailWord_2978791).sum := by decide
  have hdescent : baseEnd_2978791 < baseStart_2978791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978864 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 4, 5]
def baseStart_2978864 : Nat := 118140960795 + 2978864 * 2 ^ 59
def prefixEnd_2978864 : Nat := 4983230072969 + 3 ^ 40 * 2978864 * 2
def baseEnd_2978864 : Nat := 1019726024249958943066973

theorem tailTrace_2978864 : CollatzResearch.WordTrace tailWord_2978864 prefixEnd_2978864 1019726024249958943066973 := by
  unfold tailWord_2978864
  simp only [CollatzResearch.WordTrace]
  refine ⟨54324047940045976156347823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72432063920061301541797097 54324047940045976156347823)
  ·
    refine ⟨81486071910068964234521735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54324047940045976156347823 81486071910068964234521735)
    ·
      refine ⟨122229107865103446351782603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81486071910068964234521735 122229107865103446351782603)
      ·
        refine ⟨183343661797655169527673905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122229107865103446351782603 183343661797655169527673905)
        ·
          refine ⟨137507746348241377145755429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183343661797655169527673905 137507746348241377145755429)
          ·
            refine ⟨25782702440295258214829143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137507746348241377145755429 25782702440295258214829143)
            ·
              refine ⟨38674053660442887322243715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25782702440295258214829143 38674053660442887322243715)
              ·
                refine ⟨58011080490664330983365573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38674053660442887322243715 58011080490664330983365573)
                ·
                  refine ⟨10877077591999562059381045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58011080490664330983365573 10877077591999562059381045)
                  ·
                    refine ⟨1019726024249958943066973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10877077591999562059381045 1019726024249958943066973)
                    ·
                      rfl

theorem cell22_2978864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_2978864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978864 prefixEnd_2978864 := by exact prefixLift 2978864
  have htrace : WordTrace (prefixWord ++ tailWord_2978864) baseStart_2978864 baseEnd_2978864 := by
    simpa [prefixWord, tailWord_2978864, baseEnd_2978864] using wordTrace_append hprefix tailTrace_2978864
  have hstable : (prefixWord ++ tailWord_2978864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978864).length < 2 ^ (prefixWord ++ tailWord_2978864).sum := by decide
  have hdescent : baseEnd_2978864 < baseStart_2978864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978870 : List Nat := [5, 1, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_2978870 : Nat := 118140960795 + 2978870 * 2 ^ 59
def prefixEnd_2978870 : Nat := 4983230072969 + 3 ^ 40 * 2978870 * 2
def baseEnd_2978870 : Nat := 1019728078172576927416955

theorem tailTrace_2978870 : CollatzResearch.WordTrace tailWord_2978870 prefixEnd_2978870 1019728078172576927416955 := by
  unfold tailWord_2978870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6790519669879388458588379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72432209812046810224942709 6790519669879388458588379)
  ·
    refine ⟨10185779504819082687882569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6790519669879388458588379 10185779504819082687882569)
    ·
      refine ⟨7639334628614312015911927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10185779504819082687882569 7639334628614312015911927)
      ·
        refine ⟨11459001942921468023867891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7639334628614312015911927 11459001942921468023867891)
        ·
          refine ⟨17188502914382202035801837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11459001942921468023867891 17188502914382202035801837)
          ·
            refine ⟨6445688592893325763425689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17188502914382202035801837 6445688592893325763425689)
            ·
              refine ⟨4834266444669994322569267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6445688592893325763425689 4834266444669994322569267)
              ·
                refine ⟨7251399667004991483853901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4834266444669994322569267 7251399667004991483853901)
                ·
                  refine ⟨2719274875126871806445213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7251399667004991483853901 2719274875126871806445213)
                  ·
                    refine ⟨1019728078172576927416955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2719274875126871806445213 1019728078172576927416955)
                    ·
                      rfl

theorem cell22_2978870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_2978870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978870 prefixEnd_2978870 := by exact prefixLift 2978870
  have htrace : WordTrace (prefixWord ++ tailWord_2978870) baseStart_2978870 baseEnd_2978870 := by
    simpa [prefixWord, tailWord_2978870, baseEnd_2978870] using wordTrace_append hprefix tailTrace_2978870
  have hstable : (prefixWord ++ tailWord_2978870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978870).length < 2 ^ (prefixWord ++ tailWord_2978870).sum := by decide
  have hdescent : baseEnd_2978870 < baseStart_2978870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978941 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_2978941 : Nat := 118140960795 + 2978941 * 2 ^ 59
def prefixEnd_2978941 : Nat := 4983230072969 + 3 ^ 40 * 2978941 * 2
def baseEnd_2978941 : Nat := 1019752382923556408891737

theorem tailTrace_2978941 : CollatzResearch.WordTrace tailWord_2978941 prefixEnd_2978941 1019752382923556408891737 := by
  unfold tailWord_2978941
  simp only [CollatzResearch.WordTrace]
  refine ⟨108650904300812994463248677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72433936200541996308832451 108650904300812994463248677)
  ·
    refine ⟨20372044556402436461859127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108650904300812994463248677 20372044556402436461859127)
    ·
      refine ⟨30558066834603654692788691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20372044556402436461859127 30558066834603654692788691)
      ·
        refine ⟨45837100251905482039183037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30558066834603654692788691 45837100251905482039183037)
        ·
          refine ⟨17188912594464555764693639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45837100251905482039183037 17188912594464555764693639)
          ·
            refine ⟨25783368891696833647040459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17188912594464555764693639 25783368891696833647040459)
            ·
              refine ⟨38675053337545250470560689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25783368891696833647040459 38675053337545250470560689)
              ·
                refine ⟨29006290003158937852920517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38675053337545250470560689 29006290003158937852920517)
                ·
                  refine ⟨5438679375592300847422597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29006290003158937852920517 5438679375592300847422597)
                  ·
                    refine ⟨1019752382923556408891737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5438679375592300847422597 1019752382923556408891737)
                    ·
                      rfl

theorem cell22_2978941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_2978941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978941 prefixEnd_2978941 := by exact prefixLift 2978941
  have htrace : WordTrace (prefixWord ++ tailWord_2978941) baseStart_2978941 baseEnd_2978941 := by
    simpa [prefixWord, tailWord_2978941, baseEnd_2978941] using wordTrace_append hprefix tailTrace_2978941
  have hstable : (prefixWord ++ tailWord_2978941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978941).length < 2 ^ (prefixWord ++ tailWord_2978941).sum := by decide
  have hdescent : baseEnd_2978941 < baseStart_2978941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978958 : List Nat := [4, 1, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_2978958 : Nat := 118140960795 + 2978958 * 2 ^ 59
def prefixEnd_2978958 : Nat := 4983230072969 + 3 ^ 40 * 2978958 * 2
def baseEnd_2978958 : Nat := 1019758202370974031216685

theorem tailTrace_2978958 : CollatzResearch.WordTrace tailWord_2978958 prefixEnd_2978958 1019758202370974031216685 := by
  unfold tailWord_2978958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13581440542718925795827191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72434349561167604244411685 13581440542718925795827191)
  ·
    refine ⟨20372160814078388693740787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13581440542718925795827191 20372160814078388693740787)
    ·
      refine ⟨30558241221117583040611181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20372160814078388693740787 30558241221117583040611181)
      ·
        refine ⟨11459340457919093640229193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30558241221117583040611181 11459340457919093640229193)
        ·
          refine ⟨8594505343439320230171895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11459340457919093640229193 8594505343439320230171895)
          ·
            refine ⟨12891758015158980345257843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8594505343439320230171895 12891758015158980345257843)
            ·
              refine ⟨19337637022738470517886765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12891758015158980345257843 19337637022738470517886765)
              ·
                refine ⟨7251613883526926444207537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19337637022738470517886765 7251613883526926444207537)
                ·
                  refine ⟨5438710412645194833155653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7251613883526926444207537 5438710412645194833155653)
                  ·
                    refine ⟨1019758202370974031216685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5438710412645194833155653 1019758202370974031216685)
                    ·
                      rfl

theorem cell22_2978958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_2978958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2978958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2978958 prefixEnd_2978958 := by exact prefixLift 2978958
  have htrace : WordTrace (prefixWord ++ tailWord_2978958) baseStart_2978958 baseEnd_2978958 := by
    simpa [prefixWord, tailWord_2978958, baseEnd_2978958] using wordTrace_append hprefix tailTrace_2978958
  have hstable : (prefixWord ++ tailWord_2978958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978958).length < 2 ^ (prefixWord ++ tailWord_2978958).sum := by decide
  have hdescent : baseEnd_2978958 < baseStart_2978958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979095 : List Nat := [1, 1, 3, 4, 1, 1, 2, 4, 2, 3]
def baseStart_2979095 : Nat := 118140960795 + 2979095 * 2 ^ 59
def prefixEnd_2979095 : Nat := 4983230072969 + 3 ^ 40 * 2979095 * 2
def baseEnd_2979095 : Nat := 1019805100270751340541265

theorem tailTrace_2979095 : CollatzResearch.WordTrace tailWord_2979095 prefixEnd_2979095 1019805100270751340541265 := by
  unfold tailWord_2979095
  simp only [CollatzResearch.WordTrace]
  refine ⟨108656521142255078764354739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72437680761503385842903159 108656521142255078764354739)
  ·
    refine ⟨162984781713382618146532109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108656521142255078764354739 162984781713382618146532109)
    ·
      refine ⟨61119293142518481804949541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162984781713382618146532109 61119293142518481804949541)
      ·
        refine ⟨11459867464222215338428039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61119293142518481804949541 11459867464222215338428039)
        ·
          refine ⟨17189801196333323007642059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11459867464222215338428039 17189801196333323007642059)
          ·
            refine ⟨25784701794499984511463089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17189801196333323007642059 25784701794499984511463089)
            ·
              refine ⟨19338526345874988383597317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25784701794499984511463089 19338526345874988383597317)
              ·
                refine ⟨3625973689851560321924497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19338526345874988383597317 3625973689851560321924497)
                ·
                  refine ⟨2719480267388670241443373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3625973689851560321924497 2719480267388670241443373)
                  ·
                    refine ⟨1019805100270751340541265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2719480267388670241443373 1019805100270751340541265)
                    ·
                      rfl

theorem cell22_2979095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_2979095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979095 prefixEnd_2979095 := by exact prefixLift 2979095
  have htrace : WordTrace (prefixWord ++ tailWord_2979095) baseStart_2979095 baseEnd_2979095 := by
    simpa [prefixWord, tailWord_2979095, baseEnd_2979095] using wordTrace_append hprefix tailTrace_2979095
  have hstable : (prefixWord ++ tailWord_2979095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979095).length < 2 ^ (prefixWord ++ tailWord_2979095).sum := by decide
  have hdescent : baseEnd_2979095 < baseStart_2979095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979108 : List Nat := [2, 3, 1, 3, 1, 1, 4, 7]
def baseStart_2979108 : Nat := 118140960795 + 2979108 * 2 ^ 59
def prefixEnd_2979108 : Nat := 4983230072969 + 3 ^ 40 * 2979108 * 2
def baseEnd_2979108 : Nat := 113312172270713737774025

theorem tailTrace_2979108 : CollatzResearch.WordTrace tailWord_2979108 prefixEnd_2979108 113312172270713737774025 := by
  unfold tailWord_2979108
  simp only [CollatzResearch.WordTrace]
  refine ⟨54328497645603990992288989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72437996860805321323051985 54328497645603990992288989)
  ·
    refine ⟨20373186617101496622108371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54328497645603990992288989 20373186617101496622108371)
    ·
      refine ⟨30559779925652244933162557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20373186617101496622108371 30559779925652244933162557)
      ·
        refine ⟨11459917472119591849935959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30559779925652244933162557 11459917472119591849935959)
        ·
          refine ⟨17189876208179387774903939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11459917472119591849935959 17189876208179387774903939)
          ·
            refine ⟨25784814312269081662355909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17189876208179387774903939 25784814312269081662355909)
            ·
              refine ⟨4834652683550452811691733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25784814312269081662355909 4834652683550452811691733)
              ·
                refine ⟨113312172270713737774025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4834652683550452811691733 113312172270713737774025)
                ·
                  rfl

theorem cell22_2979108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 7].length) (baseStart_2979108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979108 prefixEnd_2979108 := by exact prefixLift 2979108
  have htrace : WordTrace (prefixWord ++ tailWord_2979108) baseStart_2979108 baseEnd_2979108 := by
    simpa [prefixWord, tailWord_2979108, baseEnd_2979108] using wordTrace_append hprefix tailTrace_2979108
  have hstable : (prefixWord ++ tailWord_2979108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979108).length < 2 ^ (prefixWord ++ tailWord_2979108).sum := by decide
  have hdescent : baseEnd_2979108 < baseStart_2979108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979112 : List Nat := [2, 1, 5, 1, 2, 2, 1, 3, 2, 3]
def baseStart_2979112 : Nat := 118140960795 + 2979112 * 2 ^ 59
def prefixEnd_2979112 : Nat := 4983230072969 + 3 ^ 40 * 2979112 * 2
def baseEnd_2979112 : Nat := 1019810919718168962866213

theorem tailTrace_2979112 : CollatzResearch.WordTrace tailWord_2979112 prefixEnd_2979112 1019810919718168962866213 := by
  unfold tailWord_2979112
  simp only [CollatzResearch.WordTrace]
  refine ⟨54328570591596745333861795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72438094122128993778482393 54328570591596745333861795)
  ·
    refine ⟨81492855887395118000792693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54328570591596745333861795 81492855887395118000792693)
    ·
      refine ⟨7639955239443292312574315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81492855887395118000792693 7639955239443292312574315)
      ·
        refine ⟨11459932859164938468861473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7639955239443292312574315 11459932859164938468861473)
        ·
          refine ⟨8594949644373703851646105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11459932859164938468861473 8594949644373703851646105)
          ·
            refine ⟨6446212233280277888734579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8594949644373703851646105 6446212233280277888734579)
            ·
              refine ⟨9669318349920416833101869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6446212233280277888734579 9669318349920416833101869)
              ·
                refine ⟨3625994381220156312413201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9669318349920416833101869 3625994381220156312413201)
                ·
                  refine ⟨2719495785915117234309901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3625994381220156312413201 2719495785915117234309901)
                  ·
                    refine ⟨1019810919718168962866213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2719495785915117234309901 1019810919718168962866213)
                    ·
                      rfl

theorem cell22_2979112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_2979112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979112 prefixEnd_2979112 := by exact prefixLift 2979112
  have htrace : WordTrace (prefixWord ++ tailWord_2979112) baseStart_2979112 baseEnd_2979112 := by
    simpa [prefixWord, tailWord_2979112, baseEnd_2979112] using wordTrace_append hprefix tailTrace_2979112
  have hstable : (prefixWord ++ tailWord_2979112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979112).length < 2 ^ (prefixWord ++ tailWord_2979112).sum := by decide
  have hdescent : baseEnd_2979112 < baseStart_2979112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979142 : List Nat := [6, 1, 1, 3, 1, 10]
def baseStart_2979142 : Nat := 118140960795 + 2979142 * 2 ^ 59
def prefixEnd_2979142 : Nat := 4983230072969 + 3 ^ 40 * 2979142 * 2
def baseEnd_2979142 : Nat := 12590385053472331908841

theorem tailTrace_2979142 : CollatzResearch.WordTrace tailWord_2979142 prefixEnd_2979142 12590385053472331908841 := by
  unfold tailWord_2979142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3395569855408900180978615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72438823582056537194210453 3395569855408900180978615)
  ·
    refine ⟨5093354783113350271467923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3395569855408900180978615 5093354783113350271467923)
    ·
      refine ⟨7640032174670025407201885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5093354783113350271467923 7640032174670025407201885)
      ·
        refine ⟨2865012065501259527700707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7640032174670025407201885 2865012065501259527700707)
        ·
          refine ⟨4297518098251889291551061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2865012065501259527700707 4297518098251889291551061)
          ·
            refine ⟨12590385053472331908841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4297518098251889291551061 12590385053472331908841)
            ·
              rfl

theorem cell22_2979142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 10].length) (baseStart_2979142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979142 prefixEnd_2979142 := by exact prefixLift 2979142
  have htrace : WordTrace (prefixWord ++ tailWord_2979142) baseStart_2979142 baseEnd_2979142 := by
    simpa [prefixWord, tailWord_2979142, baseEnd_2979142] using wordTrace_append hprefix tailTrace_2979142
  have hstable : (prefixWord ++ tailWord_2979142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979142).length < 2 ^ (prefixWord ++ tailWord_2979142).sum := by decide
  have hdescent : baseEnd_2979142 < baseStart_2979142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979168 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 1, 7]
def baseStart_2979168 : Nat := 118140960795 + 2979168 * 2 ^ 59
def prefixEnd_2979168 : Nat := 4983230072969 + 3 ^ 40 * 2979168 * 2
def baseEnd_2979168 : Nat := 1019830089662603483466041

theorem tailTrace_2979168 : CollatzResearch.WordTrace tailWord_2979168 prefixEnd_2979168 1019830089662603483466041 := by
  unfold tailWord_2979168
  simp only [CollatzResearch.WordTrace]
  refine ⟨54329591835495306115881079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72439455780660408154508105 54329591835495306115881079)
  ·
    refine ⟨81494387753242959173821619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54329591835495306115881079 81494387753242959173821619)
    ·
      refine ⟨122241581629864438760732429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81494387753242959173821619 122241581629864438760732429)
      ·
        refine ⟨45840593111199164535274661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122241581629864438760732429 45840593111199164535274661)
        ·
          refine ⟨8595111208349843350363999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45840593111199164535274661 8595111208349843350363999)
          ·
            refine ⟨12892666812524765025545999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8595111208349843350363999 12892666812524765025545999)
            ·
              refine ⟨19339000218787147538318999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12892666812524765025545999 19339000218787147538318999)
              ·
                refine ⟨29008500328180721307478499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19339000218787147538318999 29008500328180721307478499)
                ·
                  refine ⟨43512750492271081961217749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29008500328180721307478499 43512750492271081961217749)
                  ·
                    refine ⟨1019830089662603483466041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43512750492271081961217749 1019830089662603483466041)
                    ·
                      rfl

theorem cell22_2979168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_2979168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979168 prefixEnd_2979168 := by exact prefixLift 2979168
  have htrace : WordTrace (prefixWord ++ tailWord_2979168) baseStart_2979168 baseEnd_2979168 := by
    simpa [prefixWord, tailWord_2979168, baseEnd_2979168] using wordTrace_append hprefix tailTrace_2979168
  have hstable : (prefixWord ++ tailWord_2979168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979168).length < 2 ^ (prefixWord ++ tailWord_2979168).sum := by decide
  have hdescent : baseEnd_2979168 < baseStart_2979168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979170 : List Nat := [3, 3, 2, 1, 1, 1, 1, 5, 5]
def baseStart_2979170 : Nat := 118140960795 + 2979170 * 2 ^ 59
def prefixEnd_2979170 : Nat := 4983230072969 + 3 ^ 40 * 2979170 * 2
def baseEnd_2979170 : Nat := 339943591434492048305345

theorem tailTrace_2979170 : CollatzResearch.WordTrace tailWord_2979170 prefixEnd_2979170 339943591434492048305345 := by
  unfold tailWord_2979170
  simp only [CollatzResearch.WordTrace]
  refine ⟨27164814154245841643333741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72439504411322244382223309 27164814154245841643333741)
  ·
    refine ⟨10186805307842190616250153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27164814154245841643333741 10186805307842190616250153)
    ·
      refine ⟨7640103980881642962187615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10186805307842190616250153 7640103980881642962187615)
      ·
        refine ⟨11460155971322464443281423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7640103980881642962187615 11460155971322464443281423)
        ·
          refine ⟨17190233956983696664922135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11460155971322464443281423 17190233956983696664922135)
          ·
            refine ⟨25785350935475544997383203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17190233956983696664922135 25785350935475544997383203)
            ·
              refine ⟨38678026403213317496074805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25785350935475544997383203 38678026403213317496074805)
              ·
                refine ⟨3626064975301248515257013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38678026403213317496074805 3626064975301248515257013)
                ·
                  refine ⟨339943591434492048305345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3626064975301248515257013 339943591434492048305345)
                  ·
                    rfl

theorem cell22_2979170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_2979170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979170 prefixEnd_2979170 := by exact prefixLift 2979170
  have htrace : WordTrace (prefixWord ++ tailWord_2979170) baseStart_2979170 baseEnd_2979170 := by
    simpa [prefixWord, tailWord_2979170, baseEnd_2979170] using wordTrace_append hprefix tailTrace_2979170
  have hstable : (prefixWord ++ tailWord_2979170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979170).length < 2 ^ (prefixWord ++ tailWord_2979170).sum := by decide
  have hdescent : baseEnd_2979170 < baseStart_2979170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979183 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 3, 4]
def baseStart_2979183 : Nat := 118140960795 + 2979183 * 2 ^ 59
def prefixEnd_2979183 : Nat := 4983230072969 + 3 ^ 40 * 2979183 * 2
def baseEnd_2979183 : Nat := 1019835224469148444340995

theorem tailTrace_2979183 : CollatzResearch.WordTrace tailWord_2979183 prefixEnd_2979183 1019835224469148444340995 := by
  unfold tailWord_2979183
  simp only [CollatzResearch.WordTrace]
  refine ⟨108659730765936269793558203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72439820510624179862372135 108659730765936269793558203)
  ·
    refine ⟨162989596148904404690337305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108659730765936269793558203 162989596148904404690337305)
    ·
      refine ⟨122242197111678303517752979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162989596148904404690337305 122242197111678303517752979)
      ·
        refine ⟨183363295667517455276629469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122242197111678303517752979 183363295667517455276629469)
        ·
          refine ⟨68761235875319045728736051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183363295667517455276629469 68761235875319045728736051)
          ·
            refine ⟨103141853812978568593104077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68761235875319045728736051 103141853812978568593104077)
            ·
              refine ⟨38678195179866963222414029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103141853812978568593104077 38678195179866963222414029)
              ·
                refine ⟨14504323192450111208405261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38678195179866963222414029 14504323192450111208405261)
                ·
                  refine ⟨5439121197168791703151973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14504323192450111208405261 5439121197168791703151973)
                  ·
                    refine ⟨1019835224469148444340995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5439121197168791703151973 1019835224469148444340995)
                    ·
                      rfl

theorem cell22_2979183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_2979183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979183 prefixEnd_2979183 := by exact prefixLift 2979183
  have htrace : WordTrace (prefixWord ++ tailWord_2979183) baseStart_2979183 baseEnd_2979183 := by
    simpa [prefixWord, tailWord_2979183, baseEnd_2979183] using wordTrace_append hprefix tailTrace_2979183
  have hstable : (prefixWord ++ tailWord_2979183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979183).length < 2 ^ (prefixWord ++ tailWord_2979183).sum := by decide
  have hdescent : baseEnd_2979183 < baseStart_2979183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979202 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2979202 : Nat := 118140960795 + 2979202 * 2 ^ 59
def prefixEnd_2979202 : Nat := 4983230072969 + 3 ^ 40 * 2979202 * 2
def baseEnd_2979202 : Nat := 1019841728557438728115937

theorem tailTrace_2979202 : CollatzResearch.WordTrace tailWord_2979202 prefixEnd_2979202 1019841728557438728115937 := by
  unfold tailWord_2979202
  simp only [CollatzResearch.WordTrace]
  refine ⟨27165105938216859009624965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72440282501911624025666573 27165105938216859009624965)
  ·
    refine ⟨5093457363415661064304681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27165105938216859009624965 5093457363415661064304681)
    ·
      refine ⟨3820093022561745798228511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5093457363415661064304681 3820093022561745798228511)
      ·
        refine ⟨5730139533842618697342767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3820093022561745798228511 5730139533842618697342767)
        ·
          refine ⟨8595209300763928046014151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5730139533842618697342767 8595209300763928046014151)
          ·
            refine ⟨12892813951145892069021227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8595209300763928046014151 12892813951145892069021227)
            ·
              refine ⟨19339220926718838103531841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12892813951145892069021227 19339220926718838103531841)
              ·
                refine ⟨14504415695039128577648881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19339220926718838103531841 14504415695039128577648881)
                ·
                  refine ⟨10878311771279346433236661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14504415695039128577648881 10878311771279346433236661)
                  ·
                    refine ⟨1019841728557438728115937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10878311771279346433236661 1019841728557438728115937)
                    ·
                      rfl

theorem cell22_2979202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2979202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979202 prefixEnd_2979202 := by exact prefixLift 2979202
  have htrace : WordTrace (prefixWord ++ tailWord_2979202) baseStart_2979202 baseEnd_2979202 := by
    simpa [prefixWord, tailWord_2979202, baseEnd_2979202] using wordTrace_append hprefix tailTrace_2979202
  have hstable : (prefixWord ++ tailWord_2979202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979202).length < 2 ^ (prefixWord ++ tailWord_2979202).sum := by decide
  have hdescent : baseEnd_2979202 < baseStart_2979202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979273 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 2, 6]
def baseStart_2979273 : Nat := 118140960795 + 2979273 * 2 ^ 59
def prefixEnd_2979273 : Nat := 4983230072969 + 3 ^ 40 * 2979273 * 2
def baseEnd_2979273 : Nat := 1019866033308418209590719

theorem tailTrace_2979273 : CollatzResearch.WordTrace tailWord_2979273 prefixEnd_2979273 1019866033308418209590719 := by
  unfold tailWord_2979273
  simp only [CollatzResearch.WordTrace]
  refine ⟨108663013335610215164334473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72442008890406810109556315 108663013335610215164334473)
  ·
    refine ⟨81497260001707661373250855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108663013335610215164334473 81497260001707661373250855)
    ·
      refine ⟨122245890002561492059876283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81497260001707661373250855 122245890002561492059876283)
      ·
        refine ⟨183368835003842238089814425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122245890002561492059876283 183368835003842238089814425)
        ·
          refine ⟨137526626252881678567360819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183368835003842238089814425 137526626252881678567360819)
          ·
            refine ⟨206289939379322517851041229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137526626252881678567360819 206289939379322517851041229)
            ·
              refine ⟨77358727267245944194140461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206289939379322517851041229 77358727267245944194140461)
              ·
                refine ⟨29009522725217229072802673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77358727267245944194140461 29009522725217229072802673)
                ·
                  refine ⟨21757142043912921804602005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29009522725217229072802673 21757142043912921804602005)
                  ·
                    refine ⟨1019866033308418209590719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21757142043912921804602005 1019866033308418209590719)
                    ·
                      rfl

theorem cell22_2979273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_2979273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979273 prefixEnd_2979273 := by exact prefixLift 2979273
  have htrace : WordTrace (prefixWord ++ tailWord_2979273) baseStart_2979273 baseEnd_2979273 := by
    simpa [prefixWord, tailWord_2979273, baseEnd_2979273] using wordTrace_append hprefix tailTrace_2979273
  have hstable : (prefixWord ++ tailWord_2979273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979273).length < 2 ^ (prefixWord ++ tailWord_2979273).sum := by decide
  have hdescent : baseEnd_2979273 < baseStart_2979273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979399 : List Nat := [1, 1, 4, 1, 5, 2, 1, 1, 1, 5]
def baseStart_2979399 : Nat := 118140960795 + 2979399 * 2 ^ 59
def prefixEnd_2979399 : Nat := 4983230072969 + 3 ^ 40 * 2979399 * 2
def baseEnd_2979399 : Nat := 1019909165683395880940333

theorem tailTrace_2979399 : CollatzResearch.WordTrace tailWord_2979399 prefixEnd_2979399 1019909165683395880940333 := by
  unfold tailWord_2979399
  simp only [CollatzResearch.WordTrace]
  refine ⟨108667608933153738683421251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72445072622102492455614167 108667608933153738683421251)
  ·
    refine ⟨163001413399730608025131877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108667608933153738683421251 163001413399730608025131877)
    ·
      refine ⟨30562765012449489004712227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163001413399730608025131877 30562765012449489004712227)
      ·
        refine ⟨45844147518674233507068341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30562765012449489004712227 45844147518674233507068341)
        ·
          refine ⟨4297888829875709391287657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45844147518674233507068341 4297888829875709391287657)
          ·
            refine ⟨3223416622406782043465743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4297888829875709391287657 3223416622406782043465743)
            ·
              refine ⟨4835124933610173065198615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3223416622406782043465743 4835124933610173065198615)
              ·
                refine ⟨7252687400415259597797923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4835124933610173065198615 7252687400415259597797923)
                ·
                  refine ⟨10879031100622889396696885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7252687400415259597797923 10879031100622889396696885)
                  ·
                    refine ⟨1019909165683395880940333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10879031100622889396696885 1019909165683395880940333)
                    ·
                      rfl

theorem cell22_2979399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_2979399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979399 prefixEnd_2979399 := by exact prefixLift 2979399
  have htrace : WordTrace (prefixWord ++ tailWord_2979399) baseStart_2979399 baseEnd_2979399 := by
    simpa [prefixWord, tailWord_2979399, baseEnd_2979399] using wordTrace_append hprefix tailTrace_2979399
  have hstable : (prefixWord ++ tailWord_2979399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979399).length < 2 ^ (prefixWord ++ tailWord_2979399).sum := by decide
  have hdescent : baseEnd_2979399 < baseStart_2979399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979455 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 6, 5]
def baseStart_2979455 : Nat := 118140960795 + 2979455 * 2 ^ 59
def prefixEnd_2979455 : Nat := 4983230072969 + 3 ^ 40 * 2979455 * 2
def baseEnd_2979455 : Nat := 1019928335627830401540161

theorem tailTrace_2979455 : CollatzResearch.WordTrace tailWord_2979455 prefixEnd_2979455 1019928335627830401540161 := by
  unfold tailWord_2979455
  simp only [CollatzResearch.WordTrace]
  refine ⟨108669651420950860247459819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72446434280633906831639879 108669651420950860247459819)
  ·
    refine ⟨163004477131426290371189729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108669651420950860247459819 163004477131426290371189729)
    ·
      refine ⟨122253357848569717778392297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163004477131426290371189729 122253357848569717778392297)
      ·
        refine ⟨91690018386427288333794223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122253357848569717778392297 91690018386427288333794223)
        ·
          refine ⟨137535027579640932500691335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91690018386427288333794223 137535027579640932500691335)
          ·
            refine ⟨206302541369461398751037003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137535027579640932500691335 206302541369461398751037003)
            ·
              refine ⟨309453812054192098126555505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206302541369461398751037003 309453812054192098126555505)
              ·
                refine ⟨232090359040644073594916629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309453812054192098126555505 232090359040644073594916629)
                ·
                  refine ⟨10879235580030190949761717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 232090359040644073594916629 10879235580030190949761717)
                  ·
                    refine ⟨1019928335627830401540161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10879235580030190949761717 1019928335627830401540161)
                    ·
                      rfl

theorem cell22_2979455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_2979455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979455 prefixEnd_2979455 := by exact prefixLift 2979455
  have htrace : WordTrace (prefixWord ++ tailWord_2979455) baseStart_2979455 baseEnd_2979455 := by
    simpa [prefixWord, tailWord_2979455, baseEnd_2979455] using wordTrace_append hprefix tailTrace_2979455
  have hstable : (prefixWord ++ tailWord_2979455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979455).length < 2 ^ (prefixWord ++ tailWord_2979455).sum := by decide
  have hdescent : baseEnd_2979455 < baseStart_2979455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979534 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 4, 3]
def baseStart_2979534 : Nat := 118140960795 + 2979534 * 2 ^ 59
def prefixEnd_2979534 : Nat := 4983230072969 + 3 ^ 40 * 2979534 * 2
def baseEnd_2979534 : Nat := 1019955378942300528814919

theorem tailTrace_2979534 : CollatzResearch.WordTrace tailWord_2979534 prefixEnd_2979534 1019955378942300528814919 := by
  unfold tailWord_2979534
  simp only [CollatzResearch.WordTrace]
  refine ⟨13584066598458082092448207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72448355191776437826390437 13584066598458082092448207)
  ·
    refine ⟨20376099897687123138672311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13584066598458082092448207 20376099897687123138672311)
    ·
      refine ⟨30564149846530684708008467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20376099897687123138672311 30564149846530684708008467)
      ·
        refine ⟨45846224769796027062012701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30564149846530684708008467 45846224769796027062012701)
        ·
          refine ⟨17192334288673510148254763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45846224769796027062012701 17192334288673510148254763)
          ·
            refine ⟨25788501433010265222382145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17192334288673510148254763 25788501433010265222382145)
            ·
              refine ⟨19341376074757698916786609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25788501433010265222382145 19341376074757698916786609)
              ·
                refine ⟨14506032056068274187589957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19341376074757698916786609 14506032056068274187589957)
                ·
                  refine ⟨2719881010512801410173117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14506032056068274187589957 2719881010512801410173117)
                  ·
                    refine ⟨1019955378942300528814919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2719881010512801410173117 1019955378942300528814919)
                    ·
                      rfl

theorem cell22_2979534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_2979534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979534 prefixEnd_2979534 := by exact prefixLift 2979534
  have htrace : WordTrace (prefixWord ++ tailWord_2979534) baseStart_2979534 baseEnd_2979534 := by
    simpa [prefixWord, tailWord_2979534, baseEnd_2979534] using wordTrace_append hprefix tailTrace_2979534
  have hstable : (prefixWord ++ tailWord_2979534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979534).length < 2 ^ (prefixWord ++ tailWord_2979534).sum := by decide
  have hdescent : baseEnd_2979534 < baseStart_2979534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979538 : List Nat := [3, 2, 2, 2, 2, 3, 2, 1, 1, 4]
def baseStart_2979538 : Nat := 118140960795 + 2979538 * 2 ^ 59
def prefixEnd_2979538 : Nat := 4983230072969 + 3 ^ 40 * 2979538 * 2
def baseEnd_2979538 : Nat := 1019956748224045851714907

theorem tailTrace_2979538 : CollatzResearch.WordTrace tailWord_2979538 prefixEnd_2979538 1019956748224045851714907 := by
  unfold tailWord_2979538
  simp only [CollatzResearch.WordTrace]
  refine ⟨27168169669912541355682817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72448452453100110281820845 27168169669912541355682817)
  ·
    refine ⟨20376127252434406016762113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27168169669912541355682817 20376127252434406016762113)
    ·
      refine ⟨15282095439325804512571585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20376127252434406016762113 15282095439325804512571585)
      ·
        refine ⟨11461571579494353384428689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15282095439325804512571585 11461571579494353384428689)
        ·
          refine ⟨8596178684620765038321517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11461571579494353384428689 8596178684620765038321517)
          ·
            refine ⟨3223567006732786889370569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8596178684620765038321517 3223567006732786889370569)
            ·
              refine ⟨2417675255049590167027927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3223567006732786889370569 2417675255049590167027927)
              ·
                refine ⟨3626512882574385250541891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2417675255049590167027927 3626512882574385250541891)
                ·
                  refine ⟨5439769323861577875812837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3626512882574385250541891 5439769323861577875812837)
                  ·
                    refine ⟨1019956748224045851714907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5439769323861577875812837 1019956748224045851714907)
                    ·
                      rfl

theorem cell22_2979538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_2979538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979538 prefixEnd_2979538 := by exact prefixLift 2979538
  have htrace : WordTrace (prefixWord ++ tailWord_2979538) baseStart_2979538 baseEnd_2979538 := by
    simpa [prefixWord, tailWord_2979538, baseEnd_2979538] using wordTrace_append hprefix tailTrace_2979538
  have hstable : (prefixWord ++ tailWord_2979538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979538).length < 2 ^ (prefixWord ++ tailWord_2979538).sum := by decide
  have hdescent : baseEnd_2979538 < baseStart_2979538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979592 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 9]
def baseStart_2979592 : Nat := 118140960795 + 2979592 * 2 ^ 59
def prefixEnd_2979592 : Nat := 4983230072969 + 3 ^ 40 * 2979592 * 2
def baseEnd_2979592 : Nat := 339991744509202570288247

theorem tailTrace_2979592 : CollatzResearch.WordTrace tailWord_2979592 prefixEnd_2979592 339991744509202570288247 := by
  unfold tailWord_2979592
  simp only [CollatzResearch.WordTrace]
  refine ⟨54337324110727266322598515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72449765480969688430131353 54337324110727266322598515)
  ·
    refine ⟨81505986166090899483897773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54337324110727266322598515 81505986166090899483897773)
    ·
      refine ⟨30564744812284087306461665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81505986166090899483897773 30564744812284087306461665)
      ·
        refine ⟨22923558609213065479846249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30564744812284087306461665 22923558609213065479846249)
        ·
          refine ⟨17192668956909799109884687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22923558609213065479846249 17192668956909799109884687)
          ·
            refine ⟨25789003435364698664827031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17192668956909799109884687 25789003435364698664827031)
            ·
              refine ⟨38683505153047047997240547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25789003435364698664827031 38683505153047047997240547)
              ·
                refine ⟨58025257729570571995860821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38683505153047047997240547 58025257729570571995860821)
                ·
                  refine ⟨339991744509202570288247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58025257729570571995860821 339991744509202570288247)
                  ·
                    rfl

theorem cell22_2979592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 9].length) (baseStart_2979592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979592 prefixEnd_2979592 := by exact prefixLift 2979592
  have htrace : WordTrace (prefixWord ++ tailWord_2979592) baseStart_2979592 baseEnd_2979592 := by
    simpa [prefixWord, tailWord_2979592, baseEnd_2979592] using wordTrace_append hprefix tailTrace_2979592
  have hstable : (prefixWord ++ tailWord_2979592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979592).length < 2 ^ (prefixWord ++ tailWord_2979592).sum := by decide
  have hdescent : baseEnd_2979592 < baseStart_2979592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979639 : List Nat := [1, 1, 3, 1, 2, 1, 2, 6, 1, 4]
def baseStart_2979639 : Nat := 118140960795 + 2979639 * 2 ^ 59
def prefixEnd_2979639 : Nat := 4983230072969 + 3 ^ 40 * 2979639 * 2
def baseEnd_2979639 : Nat := 1019991322588115254939597

theorem tailTrace_2979639 : CollatzResearch.WordTrace tailWord_2979639 prefixEnd_2979639 1019991322588115254939597 := by
  unfold tailWord_2979639
  simp only [CollatzResearch.WordTrace]
  refine ⟨108676362452284259672157971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72450908301522839781438647 108676362452284259672157971)
  ·
    refine ⟨163014543678426389508236957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108676362452284259672157971 163014543678426389508236957)
    ·
      refine ⟨61130453879409896065588859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163014543678426389508236957 61130453879409896065588859)
      ·
        refine ⟨91695680819114844098383289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61130453879409896065588859 91695680819114844098383289)
        ·
          refine ⟨68771760614336133073787467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91695680819114844098383289 68771760614336133073787467)
          ·
            refine ⟨103157640921504199610681201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68771760614336133073787467 103157640921504199610681201)
            ·
              refine ⟨77368230691128149708010901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103157640921504199610681201 77368230691128149708010901)
              ·
                refine ⟨3626635813646632017563011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77368230691128149708010901 3626635813646632017563011)
                ·
                  refine ⟨5439953720469948026344517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3626635813646632017563011 5439953720469948026344517)
                  ·
                    refine ⟨1019991322588115254939597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5439953720469948026344517 1019991322588115254939597)
                    ·
                      rfl

theorem cell22_2979639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_2979639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979639 prefixEnd_2979639 := by exact prefixLift 2979639
  have htrace : WordTrace (prefixWord ++ tailWord_2979639) baseStart_2979639 baseEnd_2979639 := by
    simpa [prefixWord, tailWord_2979639, baseEnd_2979639] using wordTrace_append hprefix tailTrace_2979639
  have hstable : (prefixWord ++ tailWord_2979639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979639).length < 2 ^ (prefixWord ++ tailWord_2979639).sum := by decide
  have hdescent : baseEnd_2979639 < baseStart_2979639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979667 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 5, 6]
def baseStart_2979667 : Nat := 118140960795 + 2979667 * 2 ^ 59
def prefixEnd_2979667 : Nat := 4983230072969 + 3 ^ 40 * 2979667 * 2
def baseEnd_2979667 : Nat := 1020000907560332515239511

theorem tailTrace_2979667 : CollatzResearch.WordTrace tailWord_2979667 prefixEnd_2979667 1020000907560332515239511 := by
  unfold tailWord_2979667
  simp only [CollatzResearch.WordTrace]
  refine ⟨108677383696182820454177255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72451589130788546969451503 108677383696182820454177255)
  ·
    refine ⟨163016075544274230681265883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108677383696182820454177255 163016075544274230681265883)
    ·
      refine ⟨244524113316411346021898825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163016075544274230681265883 244524113316411346021898825)
      ·
        refine ⟨183393084987308509516424119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244524113316411346021898825 183393084987308509516424119)
        ·
          refine ⟨275089627480962764274636179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183393084987308509516424119 275089627480962764274636179)
          ·
            refine ⟨412634441221444146411954269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275089627480962764274636179 412634441221444146411954269)
            ·
              refine ⟨154737915458041554904482851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 412634441221444146411954269 154737915458041554904482851)
              ·
                refine ⟨232106873187062332356724277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154737915458041554904482851 232106873187062332356724277)
                ·
                  refine ⟨21760019361287093658442901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 232106873187062332356724277 21760019361287093658442901)
                  ·
                    refine ⟨1020000907560332515239511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21760019361287093658442901 1020000907560332515239511)
                    ·
                      rfl

theorem cell22_2979667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 6].length) (baseStart_2979667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979667 prefixEnd_2979667 := by exact prefixLift 2979667
  have htrace : WordTrace (prefixWord ++ tailWord_2979667) baseStart_2979667 baseEnd_2979667 := by
    simpa [prefixWord, tailWord_2979667, baseEnd_2979667] using wordTrace_append hprefix tailTrace_2979667
  have hstable : (prefixWord ++ tailWord_2979667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979667).length < 2 ^ (prefixWord ++ tailWord_2979667).sum := by decide
  have hdescent : baseEnd_2979667 < baseStart_2979667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979720 : List Nat := [2, 1, 3, 3, 3, 2, 1, 2, 2, 3]
def baseStart_2979720 : Nat := 118140960795 + 2979720 * 2 ^ 59
def prefixEnd_2979720 : Nat := 4983230072969 + 3 ^ 40 * 2979720 * 2
def baseEnd_2979720 : Nat := 1020019050543458043664349

theorem tailTrace_2979720 : CollatzResearch.WordTrace tailWord_2979720 prefixEnd_2979720 1020019050543458043664349 := by
  unfold tailWord_2979720
  simp only [CollatzResearch.WordTrace]
  refine ⟨54339658382495405252928307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72452877843327207003904409 54339658382495405252928307)
  ·
    refine ⟨81509487573743107879392461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54339658382495405252928307 81509487573743107879392461)
    ·
      refine ⟨30566057840153665454772173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81509487573743107879392461 30566057840153665454772173)
      ·
        refine ⟨11462271690057624545539565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30566057840153665454772173 11462271690057624545539565)
        ·
          refine ⟨4298351883771609204577337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11462271690057624545539565 4298351883771609204577337)
          ·
            refine ⟨3223763912828706903433003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4298351883771609204577337 3223763912828706903433003)
            ·
              refine ⟨4835645869243060355149505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3223763912828706903433003 4835645869243060355149505)
              ·
                refine ⟨3626734401932295266362129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4835645869243060355149505 3626734401932295266362129)
                ·
                  refine ⟨2720050801449221449771597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3626734401932295266362129 2720050801449221449771597)
                  ·
                    refine ⟨1020019050543458043664349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2720050801449221449771597 1020019050543458043664349)
                    ·
                      rfl

theorem cell22_2979720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_2979720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979720 prefixEnd_2979720 := by exact prefixLift 2979720
  have htrace : WordTrace (prefixWord ++ tailWord_2979720) baseStart_2979720 baseEnd_2979720 := by
    simpa [prefixWord, tailWord_2979720, baseEnd_2979720] using wordTrace_append hprefix tailTrace_2979720
  have hstable : (prefixWord ++ tailWord_2979720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979720).length < 2 ^ (prefixWord ++ tailWord_2979720).sum := by decide
  have hdescent : baseEnd_2979720 < baseStart_2979720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979765 : List Nat := [1, 3, 3, 2, 1, 2, 3, 3, 1, 3]
def baseStart_2979765 : Nat := 118140960795 + 2979765 * 2 ^ 59
def prefixEnd_2979765 : Nat := 4983230072969 + 3 ^ 40 * 2979765 * 2
def baseEnd_2979765 : Nat := 1020034454963092926289211

theorem tailTrace_2979765 : CollatzResearch.WordTrace tailWord_2979765 prefixEnd_2979765 1020034454963092926289211 := by
  unfold tailWord_2979765
  simp only [CollatzResearch.WordTrace]
  refine ⟨108680958049827783191244749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72453972033218522127496499 108680958049827783191244749)
  ·
    refine ⟨40755359268685418696716781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108680958049827783191244749 40755359268685418696716781)
    ·
      refine ⟨15283259725757032011268793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40755359268685418696716781 15283259725757032011268793)
      ·
        refine ⟨11462444794317774008451595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15283259725757032011268793 11462444794317774008451595)
        ·
          refine ⟨17193667191476661012677393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11462444794317774008451595 17193667191476661012677393)
          ·
            refine ⟨12895250393607495759508045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17193667191476661012677393 12895250393607495759508045)
            ·
              refine ⟨4835718897602810909815517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12895250393607495759508045 4835718897602810909815517)
              ·
                refine ⟨1813394586601054091180819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4835718897602810909815517 1813394586601054091180819)
                ·
                  refine ⟨2720091879901581136771229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1813394586601054091180819 2720091879901581136771229)
                  ·
                    refine ⟨1020034454963092926289211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2720091879901581136771229 1020034454963092926289211)
                    ·
                      rfl

theorem cell22_2979765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_2979765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979765 prefixEnd_2979765 := by exact prefixLift 2979765
  have htrace : WordTrace (prefixWord ++ tailWord_2979765) baseStart_2979765 baseEnd_2979765 := by
    simpa [prefixWord, tailWord_2979765, baseEnd_2979765] using wordTrace_append hprefix tailTrace_2979765
  have hstable : (prefixWord ++ tailWord_2979765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979765).length < 2 ^ (prefixWord ++ tailWord_2979765).sum := by decide
  have hdescent : baseEnd_2979765 < baseStart_2979765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979819 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 1, 6]
def baseStart_2979819 : Nat := 118140960795 + 2979819 * 2 ^ 59
def prefixEnd_2979819 : Nat := 4983230072969 + 3 ^ 40 * 2979819 * 2
def baseEnd_2979819 : Nat := 1020052940266654785439045

theorem tailTrace_2979819 : CollatzResearch.WordTrace tailWord_2979819 prefixEnd_2979819 1020052940266654785439045 := by
  unfold tailWord_2979819
  simp only [CollatzResearch.WordTrace]
  refine ⟨108682927591632150413710511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72455285061088100275807007 108682927591632150413710511)
  ·
    refine ⟨163024391387448225620565767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108682927591632150413710511 163024391387448225620565767)
    ·
      refine ⟨244536587081172338430848651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163024391387448225620565767 244536587081172338430848651)
      ·
        refine ⟨366804880621758507646272977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244536587081172338430848651 366804880621758507646272977)
        ·
          refine ⟨275103660466318880734704733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366804880621758507646272977 275103660466318880734704733)
          ·
            refine ⟨103163872674869580275514275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275103660466318880734704733 103163872674869580275514275)
            ·
              refine ⟨154745809012304370413271413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103163872674869580275514275 154745809012304370413271413)
              ·
                refine ⟨14507419594903534726244195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 154745809012304370413271413 14507419594903534726244195)
                ·
                  refine ⟨21761129392355302089366293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14507419594903534726244195 21761129392355302089366293)
                  ·
                    refine ⟨1020052940266654785439045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21761129392355302089366293 1020052940266654785439045)
                    ·
                      rfl

theorem cell22_2979819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 6].length) (baseStart_2979819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979819 prefixEnd_2979819 := by exact prefixLift 2979819
  have htrace : WordTrace (prefixWord ++ tailWord_2979819) baseStart_2979819 baseEnd_2979819 := by
    simpa [prefixWord, tailWord_2979819, baseEnd_2979819] using wordTrace_append hprefix tailTrace_2979819
  have hstable : (prefixWord ++ tailWord_2979819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979819).length < 2 ^ (prefixWord ++ tailWord_2979819).sum := by decide
  have hdescent : baseEnd_2979819 < baseStart_2979819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979825 : List Nat := [1, 2, 2, 2, 5, 1, 3, 1, 1, 4]
def baseStart_2979825 : Nat := 118140960795 + 2979825 * 2 ^ 59
def prefixEnd_2979825 : Nat := 4983230072969 + 3 ^ 40 * 2979825 * 2
def baseEnd_2979825 : Nat := 1020054994189272769789027

theorem tailTrace_2979825 : CollatzResearch.WordTrace tailWord_2979825 prefixEnd_2979825 1020054994189272769789027 := by
  unfold tailWord_2979825
  simp only [CollatzResearch.WordTrace]
  refine ⟨108683146429610413438428929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72455430953073608958952619 108683146429610413438428929)
  ·
    refine ⟨81512359822207810078821697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108683146429610413438428929 81512359822207810078821697)
    ·
      refine ⟨61134269866655857559116273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81512359822207810078821697 61134269866655857559116273)
      ·
        refine ⟨45850702399991893169337205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61134269866655857559116273 45850702399991893169337205)
        ·
          refine ⟨4298503349999239984625363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45850702399991893169337205 4298503349999239984625363)
          ·
            refine ⟨6447755024998859976938045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298503349999239984625363 6447755024998859976938045)
            ·
              refine ⟨2417908134374572491351767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6447755024998859976938045 2417908134374572491351767)
              ·
                refine ⟨3626862201561858737027651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2417908134374572491351767 3626862201561858737027651)
                ·
                  refine ⟨5440293302342788105541477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3626862201561858737027651 5440293302342788105541477)
                  ·
                    refine ⟨1020054994189272769789027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5440293302342788105541477 1020054994189272769789027)
                    ·
                      rfl

theorem cell22_2979825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 1, 4].length) (baseStart_2979825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979825 prefixEnd_2979825 := by exact prefixLift 2979825
  have htrace : WordTrace (prefixWord ++ tailWord_2979825) baseStart_2979825 baseEnd_2979825 := by
    simpa [prefixWord, tailWord_2979825, baseEnd_2979825] using wordTrace_append hprefix tailTrace_2979825
  have hstable : (prefixWord ++ tailWord_2979825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979825).length < 2 ^ (prefixWord ++ tailWord_2979825).sum := by decide
  have hdescent : baseEnd_2979825 < baseStart_2979825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979836 : List Nat := [2, 2, 2, 1, 2, 2, 1, 4, 2, 4]
def baseStart_2979836 : Nat := 118140960795 + 2979836 * 2 ^ 59
def prefixEnd_2979836 : Nat := 4983230072969 + 3 ^ 40 * 2979836 * 2
def baseEnd_2979836 : Nat := 1020058759714072407763993

theorem tailTrace_2979836 : CollatzResearch.WordTrace tailWord_2979836 prefixEnd_2979836 1020058759714072407763993 := by
  unfold tailWord_2979836
  simp only [CollatzResearch.WordTrace]
  refine ⟨54341773816285281158539681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72455698421713708211386241 54341773816285281158539681)
  ·
    refine ⟨40756330362213960868904761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54341773816285281158539681 40756330362213960868904761)
    ·
      refine ⟨30567247771660470651678571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40756330362213960868904761 30567247771660470651678571)
      ·
        refine ⟨45850871657490705977517857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30567247771660470651678571 45850871657490705977517857)
        ·
          refine ⟨34388153743118029483138393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45850871657490705977517857 34388153743118029483138393)
          ·
            refine ⟨25791115307338522112353795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34388153743118029483138393 25791115307338522112353795)
            ·
              refine ⟨38686672961007783168530693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25791115307338522112353795 38686672961007783168530693)
              ·
                refine ⟨7253751180188959344099505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38686672961007783168530693 7253751180188959344099505)
                ·
                  refine ⟨5440313385141719508074629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7253751180188959344099505 5440313385141719508074629)
                  ·
                    refine ⟨1020058759714072407763993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5440313385141719508074629 1020058759714072407763993)
                    ·
                      rfl

theorem cell22_2979836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_2979836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979836 prefixEnd_2979836 := by exact prefixLift 2979836
  have htrace : WordTrace (prefixWord ++ tailWord_2979836) baseStart_2979836 baseEnd_2979836 := by
    simpa [prefixWord, tailWord_2979836, baseEnd_2979836] using wordTrace_append hprefix tailTrace_2979836
  have hstable : (prefixWord ++ tailWord_2979836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979836).length < 2 ^ (prefixWord ++ tailWord_2979836).sum := by decide
  have hdescent : baseEnd_2979836 < baseStart_2979836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979849 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 4, 7]
def baseStart_2979849 : Nat := 118140960795 + 2979849 * 2 ^ 59
def prefixEnd_2979849 : Nat := 4983230072969 + 3 ^ 40 * 2979849 * 2
def baseEnd_2979849 : Nat := 1020063209879744707188953

theorem tailTrace_2979849 : CollatzResearch.WordTrace tailWord_2979849 prefixEnd_2979849 1020063209879744707188953 := by
  unfold tailWord_2979849
  simp only [CollatzResearch.WordTrace]
  refine ⟨108684021781523465537302601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72456014521015643691535067 108684021781523465537302601)
  ·
    refine ⟨81513016336142599152976951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108684021781523465537302601 81513016336142599152976951)
    ·
      refine ⟨122269524504213898729465427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81513016336142599152976951 122269524504213898729465427)
      ·
        refine ⟨183404286756320848094198141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122269524504213898729465427 183404286756320848094198141)
        ·
          refine ⟨68776607533620318035324303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183404286756320848094198141 68776607533620318035324303)
          ·
            refine ⟨103164911300430477052986455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68776607533620318035324303 103164911300430477052986455)
            ·
              refine ⟨154747366950645715579479683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103164911300430477052986455 154747366950645715579479683)
              ·
                refine ⟨232121050425968573369219525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154747366950645715579479683 232121050425968573369219525)
                ·
                  refine ⟨43522696954869107506728661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 232121050425968573369219525 43522696954869107506728661)
                  ·
                    refine ⟨1020063209879744707188953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43522696954869107506728661 1020063209879744707188953)
                    ·
                      rfl

theorem cell22_2979849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_2979849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979849 prefixEnd_2979849 := by exact prefixLift 2979849
  have htrace : WordTrace (prefixWord ++ tailWord_2979849) baseStart_2979849 baseEnd_2979849 := by
    simpa [prefixWord, tailWord_2979849, baseEnd_2979849] using wordTrace_append hprefix tailTrace_2979849
  have hstable : (prefixWord ++ tailWord_2979849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979849).length < 2 ^ (prefixWord ++ tailWord_2979849).sum := by decide
  have hdescent : baseEnd_2979849 < baseStart_2979849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979868 : List Nat := [2, 2, 3, 1, 3, 2, 3, 6]
def baseStart_2979868 : Nat := 118140960795 + 2979868 * 2 ^ 59
def prefixEnd_2979868 : Nat := 4983230072969 + 3 ^ 40 * 2979868 * 2
def baseEnd_2979868 : Nat := 113341079329781665662655

theorem tailTrace_2979868 : CollatzResearch.WordTrace tailWord_2979868 prefixEnd_2979868 113341079329781665662655 := by
  unfold tailWord_2979868
  simp only [CollatzResearch.WordTrace]
  refine ⟨54342357384227315891122129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72456476512303087854829505 54342357384227315891122129)
  ·
    refine ⟨40756768038170486918341597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54342357384227315891122129 40756768038170486918341597)
    ·
      refine ⟨15283788014313932594378099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40756768038170486918341597 15283788014313932594378099)
      ·
        refine ⟨22925682021470898891567149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15283788014313932594378099 22925682021470898891567149)
        ·
          refine ⟨8597130758051587084337681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22925682021470898891567149 8597130758051587084337681)
          ·
            refine ⟨6447848068538690313253261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8597130758051587084337681 6447848068538690313253261)
            ·
              refine ⟨2417943025702008867469973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6447848068538690313253261 2417943025702008867469973)
              ·
                refine ⟨113341079329781665662655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2417943025702008867469973 113341079329781665662655)
                ·
                  rfl

theorem cell22_2979868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 6].length) (baseStart_2979868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979868 prefixEnd_2979868 := by exact prefixLift 2979868
  have htrace : WordTrace (prefixWord ++ tailWord_2979868) baseStart_2979868 baseEnd_2979868 := by
    simpa [prefixWord, tailWord_2979868, baseEnd_2979868] using wordTrace_append hprefix tailTrace_2979868
  have hstable : (prefixWord ++ tailWord_2979868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979868).length < 2 ^ (prefixWord ++ tailWord_2979868).sum := by decide
  have hdescent : baseEnd_2979868 < baseStart_2979868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979900 : List Nat := [2, 2, 2, 2, 2, 1, 1, 6, 1, 3]
def baseStart_2979900 : Nat := 118140960795 + 2979900 * 2 ^ 59
def prefixEnd_2979900 : Nat := 4983230072969 + 3 ^ 40 * 2979900 * 2
def baseEnd_2979900 : Nat := 1020080668221997574163797

theorem tailTrace_2979900 : CollatzResearch.WordTrace tailWord_2979900 prefixEnd_2979900 1020080668221997574163797 := by
  unfold tailWord_2979900
  simp only [CollatzResearch.WordTrace]
  refine ⟨54342940952169350623704577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72457254602892467498272769 54342940952169350623704577)
  ·
    refine ⟨40757205714127012967778433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54342940952169350623704577 40757205714127012967778433)
    ·
      refine ⟨30567904285595259725833825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40757205714127012967778433 30567904285595259725833825)
      ·
        refine ⟨22925928214196444794375369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30567904285595259725833825 22925928214196444794375369)
        ·
          refine ⟨17194446160647333595781527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22925928214196444794375369 17194446160647333595781527)
          ·
            refine ⟨25791669240971000393672291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17194446160647333595781527 25791669240971000393672291)
            ·
              refine ⟨38687503861456500590508437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25791669240971000393672291 38687503861456500590508437)
              ·
                refine ⟨1813476743505773465180083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38687503861456500590508437 1813476743505773465180083)
                ·
                  refine ⟨2720215115258660197770125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1813476743505773465180083 2720215115258660197770125)
                  ·
                    refine ⟨1020080668221997574163797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2720215115258660197770125 1020080668221997574163797)
                    ·
                      rfl

theorem cell22_2979900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_2979900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979900 prefixEnd_2979900 := by exact prefixLift 2979900
  have htrace : WordTrace (prefixWord ++ tailWord_2979900) baseStart_2979900 baseEnd_2979900 := by
    simpa [prefixWord, tailWord_2979900, baseEnd_2979900] using wordTrace_append hprefix tailTrace_2979900
  have hstable : (prefixWord ++ tailWord_2979900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979900).length < 2 ^ (prefixWord ++ tailWord_2979900).sum := by decide
  have hdescent : baseEnd_2979900 < baseStart_2979900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979911 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 2, 5]
def baseStart_2979911 : Nat := 118140960795 + 2979911 * 2 ^ 59
def prefixEnd_2979911 : Nat := 4983230072969 + 3 ^ 40 * 2979911 * 2
def baseEnd_2979911 : Nat := 1020084433746797212138763

theorem tailTrace_2979911 : CollatzResearch.WordTrace tailWord_2979911 prefixEnd_2979911 1020084433746797212138763 := by
  unfold tailWord_2979911
  simp only [CollatzResearch.WordTrace]
  refine ⟨108686283107298850126059587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72457522071532566750706391 108686283107298850126059587)
  ·
    refine ⟨163029424660948275189089381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108686283107298850126059587 163029424660948275189089381)
    ·
      refine ⟨30568017123927801597954259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163029424660948275189089381 30568017123927801597954259)
      ·
        refine ⟨45852025685891702396931389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30568017123927801597954259 45852025685891702396931389)
        ·
          refine ⟨17194509632209388398849271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45852025685891702396931389 17194509632209388398849271)
          ·
            refine ⟨25791764448314082598273907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17194509632209388398849271 25791764448314082598273907)
            ·
              refine ⟨38687646672471123897410861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25791764448314082598273907 38687646672471123897410861)
              ·
                refine ⟨14507867502176671461529073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38687646672471123897410861 14507867502176671461529073)
                ·
                  refine ⟨10880900626632503596146805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14507867502176671461529073 10880900626632503596146805)
                  ·
                    refine ⟨1020084433746797212138763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10880900626632503596146805 1020084433746797212138763)
                    ·
                      rfl

theorem cell22_2979911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_2979911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979911 prefixEnd_2979911 := by exact prefixLift 2979911
  have htrace : WordTrace (prefixWord ++ tailWord_2979911) baseStart_2979911 baseEnd_2979911 := by
    simpa [prefixWord, tailWord_2979911, baseEnd_2979911] using wordTrace_append hprefix tailTrace_2979911
  have hstable : (prefixWord ++ tailWord_2979911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979911).length < 2 ^ (prefixWord ++ tailWord_2979911).sum := by decide
  have hdescent : baseEnd_2979911 < baseStart_2979911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979913 : List Nat := [1, 2, 1, 1, 2, 2, 7, 1, 5]
def baseStart_2979913 : Nat := 118140960795 + 2979913 * 2 ^ 59
def prefixEnd_2979913 : Nat := 4983230072969 + 3 ^ 40 * 2979913 * 2
def baseEnd_2979913 : Nat := 340028372795889957862919

theorem tailTrace_2979913 : CollatzResearch.WordTrace tailWord_2979913 prefixEnd_2979913 340028372795889957862919 := by
  unfold tailWord_2979913
  simp only [CollatzResearch.WordTrace]
  refine ⟨108686356053291604467632393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72457570702194402978421595 108686356053291604467632393)
  ·
    refine ⟨81514767039968703350724295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108686356053291604467632393 81514767039968703350724295)
    ·
      refine ⟨122272150559953055026086443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81514767039968703350724295 122272150559953055026086443)
      ·
        refine ⟨183408225839929582539129665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122272150559953055026086443 183408225839929582539129665)
        ·
          refine ⟨137556169379947186904347249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183408225839929582539129665 137556169379947186904347249)
          ·
            refine ⟨103167127034960390178260437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137556169379947186904347249 103167127034960390178260437)
            ·
              refine ⟨2417979539881884144802979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 103167127034960390178260437 2417979539881884144802979)
              ·
                refine ⟨3626969309822826217204469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2417979539881884144802979 3626969309822826217204469)
                ·
                  refine ⟨340028372795889957862919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3626969309822826217204469 340028372795889957862919)
                  ·
                    rfl

theorem cell22_2979913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 5].length) (baseStart_2979913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979913 prefixEnd_2979913 := by exact prefixLift 2979913
  have htrace : WordTrace (prefixWord ++ tailWord_2979913) baseStart_2979913 baseEnd_2979913 := by
    simpa [prefixWord, tailWord_2979913, baseEnd_2979913] using wordTrace_append hprefix tailTrace_2979913
  have hstable : (prefixWord ++ tailWord_2979913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979913).length < 2 ^ (prefixWord ++ tailWord_2979913).sum := by decide
  have hdescent : baseEnd_2979913 < baseStart_2979913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979943 : List Nat := [1, 1, 5, 1, 1, 2, 1, 5, 1, 4]
def baseStart_2979943 : Nat := 118140960795 + 2979943 * 2 ^ 59
def prefixEnd_2979943 : Nat := 4983230072969 + 3 ^ 40 * 2979943 * 2
def baseEnd_2979943 : Nat := 1020095388000759795338665

theorem tailTrace_2979943 : CollatzResearch.WordTrace tailWord_2979943 prefixEnd_2979943 1020095388000759795338665 := by
  unfold tailWord_2979943
  simp only [CollatzResearch.WordTrace]
  refine ⟨108687450243182919591224483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72458300162121946394149655 108687450243182919591224483)
  ·
    refine ⟨163031175364774379386836725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108687450243182919591224483 163031175364774379386836725)
    ·
      refine ⟨15284172690447598067515943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163031175364774379386836725 15284172690447598067515943)
      ·
        refine ⟨22926259035671397101273915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15284172690447598067515943 22926259035671397101273915)
        ·
          refine ⟨34389388553507095651910873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22926259035671397101273915 34389388553507095651910873)
          ·
            refine ⟨25792041415130321738933155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34389388553507095651910873 25792041415130321738933155)
            ·
              refine ⟨38688062122695482608399733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25792041415130321738933155 38688062122695482608399733)
              ·
                refine ⟨3627005824002701494537475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38688062122695482608399733 3627005824002701494537475)
                ·
                  refine ⟨5440508736004052241806213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3627005824002701494537475 5440508736004052241806213)
                  ·
                    refine ⟨1020095388000759795338665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5440508736004052241806213 1020095388000759795338665)
                    ·
                      rfl

theorem cell22_2979943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_2979943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2979943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2979943 prefixEnd_2979943 := by exact prefixLift 2979943
  have htrace : WordTrace (prefixWord ++ tailWord_2979943) baseStart_2979943 baseEnd_2979943 := by
    simpa [prefixWord, tailWord_2979943, baseEnd_2979943] using wordTrace_append hprefix tailTrace_2979943
  have hstable : (prefixWord ++ tailWord_2979943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979943).length < 2 ^ (prefixWord ++ tailWord_2979943).sum := by decide
  have hdescent : baseEnd_2979943 < baseStart_2979943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980031 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 9]
def baseStart_2980031 : Nat := 118140960795 + 2980031 * 2 ^ 59
def prefixEnd_2980031 : Nat := 4983230072969 + 3 ^ 40 * 2980031 * 2
def baseEnd_2980031 : Nat := 340041837399718966379465

theorem tailTrace_2980031 : CollatzResearch.WordTrace tailWord_2980031 prefixEnd_2980031 340041837399718966379465 := by
  unfold tailWord_2980031
  simp only [CollatzResearch.WordTrace]
  refine ⟨108690659866864110620427947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72460439911242740413618631 108690659866864110620427947)
  ·
    refine ⟨163035989800296165930641921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108690659866864110620427947 163035989800296165930641921)
    ·
      refine ⟨122276992350222124447981441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163035989800296165930641921 122276992350222124447981441)
      ·
        refine ⟨91707744262666593335986081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122276992350222124447981441 91707744262666593335986081)
        ·
          refine ⟨68780808196999945001989561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91707744262666593335986081 68780808196999945001989561)
          ·
            refine ⟨51585606147749958751492171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68780808196999945001989561 51585606147749958751492171)
            ·
              refine ⟨77378409221624938127238257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51585606147749958751492171 77378409221624938127238257)
              ·
                refine ⟨58033806916218703595428693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77378409221624938127238257 58033806916218703595428693)
                ·
                  refine ⟨340041837399718966379465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58033806916218703595428693 340041837399718966379465)
                  ·
                    rfl

theorem cell22_2980031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 9].length) (baseStart_2980031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980031 prefixEnd_2980031 := by exact prefixLift 2980031
  have htrace : WordTrace (prefixWord ++ tailWord_2980031) baseStart_2980031 baseEnd_2980031 := by
    simpa [prefixWord, tailWord_2980031, baseEnd_2980031] using wordTrace_append hprefix tailTrace_2980031
  have hstable : (prefixWord ++ tailWord_2980031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980031).length < 2 ^ (prefixWord ++ tailWord_2980031).sum := by decide
  have hdescent : baseEnd_2980031 < baseStart_2980031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980082 : List Nat := [3, 2, 1, 3, 2, 2, 3, 1, 5]
def baseStart_2980082 : Nat := 118140960795 + 2980082 * 2 ^ 59
def prefixEnd_2980082 : Nat := 4983230072969 + 3 ^ 40 * 2980082 * 2
def baseEnd_2980082 : Nat := 340047656847136588704413

theorem tailTrace_2980082 : CollatzResearch.WordTrace tailWord_2980082 prefixEnd_2980082 340047656847136588704413 := by
  unfold tailWord_2980082
  simp only [CollatzResearch.WordTrace]
  refine ⟨27173129997419836582633625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72461679993119564220356333 27173129997419836582633625)
  ·
    refine ⟨20379847498064877436975219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27173129997419836582633625 20379847498064877436975219)
    ·
      refine ⟨30569771247097316155462829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20379847498064877436975219 30569771247097316155462829)
      ·
        refine ⟨11463664217661493558298561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30569771247097316155462829 11463664217661493558298561)
        ·
          refine ⟨8597748163246120168723921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11463664217661493558298561 8597748163246120168723921)
          ·
            refine ⟨6448311122434590126542941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8597748163246120168723921 6448311122434590126542941)
            ·
              refine ⟨2418116670912971297453603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6448311122434590126542941 2418116670912971297453603)
              ·
                refine ⟨3627175006369456946180405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2418116670912971297453603 3627175006369456946180405)
                ·
                  refine ⟨340047656847136588704413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3627175006369456946180405 340047656847136588704413)
                  ·
                    rfl

theorem cell22_2980082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_2980082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980082 prefixEnd_2980082 := by exact prefixLift 2980082
  have htrace : WordTrace (prefixWord ++ tailWord_2980082) baseStart_2980082 baseEnd_2980082 := by
    simpa [prefixWord, tailWord_2980082, baseEnd_2980082] using wordTrace_append hprefix tailTrace_2980082
  have hstable : (prefixWord ++ tailWord_2980082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980082).length < 2 ^ (prefixWord ++ tailWord_2980082).sum := by decide
  have hdescent : baseEnd_2980082 < baseStart_2980082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980095 : List Nat := [1, 1, 2, 2, 1, 4, 4, 2, 1, 4]
def baseStart_2980095 : Nat := 118140960795 + 2980095 * 2 ^ 59
def prefixEnd_2980095 : Nat := 4983230072969 + 3 ^ 40 * 2980095 * 2
def baseEnd_2980095 : Nat := 1020147420707082065538199

theorem tailTrace_2980095 : CollatzResearch.WordTrace tailWord_2980095 prefixEnd_2980095 1020147420707082065538199 := by
  unfold tailWord_2980095
  simp only [CollatzResearch.WordTrace]
  refine ⟨108692994138632249550757739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72461996092421499700505159 108692994138632249550757739)
  ·
    refine ⟨163039491207948374326136609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108692994138632249550757739 163039491207948374326136609)
    ·
      refine ⟨122279618405961280744602457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163039491207948374326136609 122279618405961280744602457)
      ·
        refine ⟨91709713804470960558451843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122279618405961280744602457 91709713804470960558451843)
        ·
          refine ⟨137564570706706440837677765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91709713804470960558451843 137564570706706440837677765)
          ·
            refine ⟨25793357007507457657064581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137564570706706440837677765 25793357007507457657064581)
            ·
              refine ⟨4836254438907648310699609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25793357007507457657064581 4836254438907648310699609)
              ·
                refine ⟨3627190829180736233024707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4836254438907648310699609 3627190829180736233024707)
                ·
                  refine ⟨5440786243771104349537061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3627190829180736233024707 5440786243771104349537061)
                  ·
                    refine ⟨1020147420707082065538199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5440786243771104349537061 1020147420707082065538199)
                    ·
                      rfl

theorem cell22_2980095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 4].length) (baseStart_2980095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980095 prefixEnd_2980095 := by exact prefixLift 2980095
  have htrace : WordTrace (prefixWord ++ tailWord_2980095) baseStart_2980095 baseEnd_2980095 := by
    simpa [prefixWord, tailWord_2980095, baseEnd_2980095] using wordTrace_append hprefix tailTrace_2980095
  have hstable : (prefixWord ++ tailWord_2980095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980095).length < 2 ^ (prefixWord ++ tailWord_2980095).sum := by decide
  have hdescent : baseEnd_2980095 < baseStart_2980095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
