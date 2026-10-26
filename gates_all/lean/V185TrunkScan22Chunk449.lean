import V185TrunkScan22Chunk448

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4001282 : List Nat := [3, 4, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_4001282 : Nat := 118140960795 + 4001282 * 2 ^ 59
def prefixEnd_4001282 : Nat := 4983230072969 + 3 ^ 40 * 4001282 * 2
def baseEnd_4001282 : Nat := 1369720600122346132982297

theorem tailTrace_4001282 : CollatzResearch.WordTrace tailWord_4001282 prefixEnd_4001282 1369720600122346132982297 := by
  unfold tailWord_4001282
  simp only [CollatzResearch.WordTrace]
  refine ⟨36484685972511538351319525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97292495926697435603518733 36484685972511538351319525)
  ·
    refine ⟨6840878619845913440872411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36484685972511538351319525 6840878619845913440872411)
    ·
      refine ⟨10261317929768870161308617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6840878619845913440872411 10261317929768870161308617)
      ·
        refine ⟨7695988447326652620981463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10261317929768870161308617 7695988447326652620981463)
        ·
          refine ⟨11543982670989978931472195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7695988447326652620981463 11543982670989978931472195)
          ·
            refine ⟨17315974006484968397208293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11543982670989978931472195 17315974006484968397208293)
            ·
              refine ⟨3246745126215931574476555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17315974006484968397208293 3246745126215931574476555)
              ·
                refine ⟨4870117689323897361714833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3246745126215931574476555 4870117689323897361714833)
                ·
                  refine ⟨3652588266992923021286125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4870117689323897361714833 3652588266992923021286125)
                  ·
                    refine ⟨1369720600122346132982297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3652588266992923021286125 1369720600122346132982297)
                    ·
                      rfl

theorem cell22_4001282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_4001282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001282 prefixEnd_4001282 := by exact prefixLift 4001282
  have htrace : WordTrace (prefixWord ++ tailWord_4001282) baseStart_4001282 baseEnd_4001282 := by
    simpa [prefixWord, tailWord_4001282, baseEnd_4001282] using wordTrace_append hprefix tailTrace_4001282
  have hstable : (prefixWord ++ tailWord_4001282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001282).length < 2 ^ (prefixWord ++ tailWord_4001282).sum := by decide
  have hdescent : baseEnd_4001282 < baseStart_4001282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001286 : List Nat := [6, 2, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_4001286 : Nat := 118140960795 + 4001286 * 2 ^ 59
def prefixEnd_4001286 : Nat := 4983230072969 + 3 ^ 40 * 4001286 * 2
def baseEnd_4001286 : Nat := 1369721969404091455882285

theorem tailTrace_4001286 : CollatzResearch.WordTrace tailWord_4001286 prefixEnd_4001286 1369721969404091455882285 := by
  unfold tailWord_4001286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4560590305688489440263241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97292593188021108058949141 4560590305688489440263241)
  ·
    refine ⟨3420442729266367080197431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4560590305688489440263241 3420442729266367080197431)
    ·
      refine ⟨5130664093899550620296147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3420442729266367080197431 5130664093899550620296147)
      ·
        refine ⟨7695996140849325930444221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5130664093899550620296147 7695996140849325930444221)
        ·
          refine ⟨2885998552818497223916583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7695996140849325930444221 2885998552818497223916583)
          ·
            refine ⟨4328997829227745835874875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885998552818497223916583 4328997829227745835874875)
            ·
              refine ⟨6493496743841618753812313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4328997829227745835874875 6493496743841618753812313)
              ·
                refine ⟨4870122557881214065359235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6493496743841618753812313 4870122557881214065359235)
                ·
                  refine ⟨7305183836821821098038853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4870122557881214065359235 7305183836821821098038853)
                  ·
                    refine ⟨1369721969404091455882285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7305183836821821098038853 1369721969404091455882285)
                    ·
                      rfl

theorem cell22_4001286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_4001286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001286 prefixEnd_4001286 := by exact prefixLift 4001286
  have htrace : WordTrace (prefixWord ++ tailWord_4001286) baseStart_4001286 baseEnd_4001286 := by
    simpa [prefixWord, tailWord_4001286, baseEnd_4001286] using wordTrace_append hprefix tailTrace_4001286
  have hstable : (prefixWord ++ tailWord_4001286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001286).length < 2 ^ (prefixWord ++ tailWord_4001286).sum := by decide
  have hdescent : baseEnd_4001286 < baseStart_4001286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001336 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 3, 4]
def baseStart_4001336 : Nat := 118140960795 + 4001336 * 2 ^ 59
def prefixEnd_4001336 : Nat := 4983230072969 + 3 ^ 40 * 4001336 * 2
def baseEnd_4001336 : Nat := 1369739085425907992132131

theorem tailTrace_4001336 : CollatzResearch.WordTrace tailWord_4001336 prefixEnd_4001336 1369739085425907992132131 := by
  unfold tailWord_4001336
  simp only [CollatzResearch.WordTrace]
  refine ⟨72970356715925260313871931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97293808954567013751829241 72970356715925260313871931)
  ·
    refine ⟨109455535073887890470807897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72970356715925260313871931 109455535073887890470807897)
    ·
      refine ⟨82091651305415917853105923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109455535073887890470807897 82091651305415917853105923)
      ·
        refine ⟨123137476958123876779658885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82091651305415917853105923 123137476958123876779658885)
        ·
          refine ⟨23088276929648226896186041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123137476958123876779658885 23088276929648226896186041)
          ·
            refine ⟨17316207697236170172139531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23088276929648226896186041 17316207697236170172139531)
            ·
              refine ⟨25974311545854255258209297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17316207697236170172139531 25974311545854255258209297)
              ·
                refine ⟨19480733659390691443656973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25974311545854255258209297 19480733659390691443656973)
                ·
                  refine ⟨7305275122271509291371365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19480733659390691443656973 7305275122271509291371365)
                  ·
                    refine ⟨1369739085425907992132131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7305275122271509291371365 1369739085425907992132131)
                    ·
                      rfl

theorem cell22_4001336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_4001336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001336 prefixEnd_4001336 := by exact prefixLift 4001336
  have htrace : WordTrace (prefixWord ++ tailWord_4001336) baseStart_4001336 baseEnd_4001336 := by
    simpa [prefixWord, tailWord_4001336, baseEnd_4001336] using wordTrace_append hprefix tailTrace_4001336
  have hstable : (prefixWord ++ tailWord_4001336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001336).length < 2 ^ (prefixWord ++ tailWord_4001336).sum := by decide
  have hdescent : baseEnd_4001336 < baseStart_4001336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001398 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_4001398 : Nat := 118140960795 + 4001398 * 2 ^ 59
def prefixEnd_4001398 : Nat := 4983230072969 + 3 ^ 40 * 4001398 * 2
def baseEnd_4001398 : Nat := 1369760309292960497081941

theorem tailTrace_4001398 : CollatzResearch.WordTrace tailWord_4001398 prefixEnd_4001398 1369760309292960497081941 := by
  unfold tailWord_4001398
  simp only [CollatzResearch.WordTrace]
  refine ⟨9121435922351619076031303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97295316505083936811000565 9121435922351619076031303)
  ·
    refine ⟨13682153883527428614046955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9121435922351619076031303 13682153883527428614046955)
    ·
      refine ⟨20523230825291142921070433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13682153883527428614046955 20523230825291142921070433)
      ·
        refine ⟨15392423118968357190802825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20523230825291142921070433 15392423118968357190802825)
        ·
          refine ⟨11544317339226267893102119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15392423118968357190802825 11544317339226267893102119)
          ·
            refine ⟨17316476008839401839653179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11544317339226267893102119 17316476008839401839653179)
            ·
              refine ⟨25974714013259102759479769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17316476008839401839653179 25974714013259102759479769)
              ·
                refine ⟨19481035509944327069609827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25974714013259102759479769 19481035509944327069609827)
                ·
                  refine ⟨29221553264916490604414741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19481035509944327069609827 29221553264916490604414741)
                  ·
                    refine ⟨1369760309292960497081941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29221553264916490604414741 1369760309292960497081941)
                    ·
                      rfl

theorem cell22_4001398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_4001398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001398 prefixEnd_4001398 := by exact prefixLift 4001398
  have htrace : WordTrace (prefixWord ++ tailWord_4001398) baseStart_4001398 baseEnd_4001398 := by
    simpa [prefixWord, tailWord_4001398, baseEnd_4001398] using wordTrace_append hprefix tailTrace_4001398
  have hstable : (prefixWord ++ tailWord_4001398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001398).length < 2 ^ (prefixWord ++ tailWord_4001398).sum := by decide
  have hdescent : baseEnd_4001398 < baseStart_4001398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001445 : List Nat := [1, 3, 1, 2, 1, 2, 2, 6, 1, 3]
def baseStart_4001445 : Nat := 118140960795 + 4001445 * 2 ^ 59
def prefixEnd_4001445 : Nat := 4983230072969 + 3 ^ 40 * 4001445 * 2
def baseEnd_4001445 : Nat := 1369776398353468041156797

theorem tailTrace_4001445 : CollatzResearch.WordTrace tailWord_4001445 prefixEnd_4001445 1369776398353468041156797 := by
  unfold tailWord_4001445
  simp only [CollatzResearch.WordTrace]
  refine ⟨145944688988455632243461789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97296459325637088162307859 145944688988455632243461789)
  ·
    refine ⟨54729258370670862091298171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145944688988455632243461789 54729258370670862091298171)
    ·
      refine ⟨82093887556006293136947257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54729258370670862091298171 82093887556006293136947257)
      ·
        refine ⟨61570415667004719852710443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82093887556006293136947257 61570415667004719852710443)
        ·
          refine ⟨92355623500507079779065665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61570415667004719852710443 92355623500507079779065665)
          ·
            refine ⟨69266717625380309834299249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92355623500507079779065665 69266717625380309834299249)
            ·
              refine ⟨51950038219035232375724437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69266717625380309834299249 51950038219035232375724437)
              ·
                refine ⟨2435158041517276517612083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51950038219035232375724437 2435158041517276517612083)
                ·
                  refine ⟨3652737062275914776418125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435158041517276517612083 3652737062275914776418125)
                  ·
                    refine ⟨1369776398353468041156797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3652737062275914776418125 1369776398353468041156797)
                    ·
                      rfl

theorem cell22_4001445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 1, 3].length) (baseStart_4001445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001445 prefixEnd_4001445 := by exact prefixLift 4001445
  have htrace : WordTrace (prefixWord ++ tailWord_4001445) baseStart_4001445 baseEnd_4001445 := by
    simpa [prefixWord, tailWord_4001445, baseEnd_4001445] using wordTrace_append hprefix tailTrace_4001445
  have hstable : (prefixWord ++ tailWord_4001445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001445).length < 2 ^ (prefixWord ++ tailWord_4001445).sum := by decide
  have hdescent : baseEnd_4001445 < baseStart_4001445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001456 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 2, 5]
def baseStart_4001456 : Nat := 118140960795 + 4001456 * 2 ^ 59
def prefixEnd_4001456 : Nat := 4983230072969 + 3 ^ 40 * 4001456 * 2
def baseEnd_4001456 : Nat := 1369780163878267679131763

theorem tailTrace_4001456 : CollatzResearch.WordTrace tailWord_4001456 prefixEnd_4001456 1369780163878267679131763 := by
  unfold tailWord_4001456
  simp only [CollatzResearch.WordTrace]
  refine ⟨72972545095707890561056111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97296726794277187414741481 72972545095707890561056111)
  ·
    refine ⟨109458817643561835841584167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72972545095707890561056111 109458817643561835841584167)
    ·
      refine ⟨164188226465342753762376251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109458817643561835841584167 164188226465342753762376251)
      ·
        refine ⟨246282339698014130643564377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164188226465342753762376251 246282339698014130643564377)
        ·
          refine ⟨184711754773510597982673283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246282339698014130643564377 184711754773510597982673283)
          ·
            refine ⟨277067632160265896974009925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184711754773510597982673283 277067632160265896974009925)
            ·
              refine ⟨51950181030049855682626861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277067632160265896974009925 51950181030049855682626861)
              ·
                refine ⟨19481317886268695880985073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51950181030049855682626861 19481317886268695880985073)
                ·
                  refine ⟨14610988414701521910738805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19481317886268695880985073 14610988414701521910738805)
                  ·
                    refine ⟨1369780163878267679131763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14610988414701521910738805 1369780163878267679131763)
                    ·
                      rfl

theorem cell22_4001456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_4001456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001456 prefixEnd_4001456 := by exact prefixLift 4001456
  have htrace : WordTrace (prefixWord ++ tailWord_4001456) baseStart_4001456 baseEnd_4001456 := by
    simpa [prefixWord, tailWord_4001456, baseEnd_4001456] using wordTrace_append hprefix tailTrace_4001456
  have hstable : (prefixWord ++ tailWord_4001456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001456).length < 2 ^ (prefixWord ++ tailWord_4001456).sum := by decide
  have hdescent : baseEnd_4001456 < baseStart_4001456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001533 : List Nat := [1, 4, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_4001533 : Nat := 118140960795 + 4001533 * 2 ^ 59
def prefixEnd_4001533 : Nat := 4983230072969 + 3 ^ 40 * 4001533 * 2
def baseEnd_4001533 : Nat := 1369806522551865144956527

theorem tailTrace_4001533 : CollatzResearch.WordTrace tailWord_4001533 prefixEnd_4001533 1369806522551865144956527 := by
  unfold tailWord_4001533
  simp only [CollatzResearch.WordTrace]
  refine ⟨145947898612136823272665253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97298599074757882181776835 145947898612136823272665253)
  ·
    refine ⟨27365230989775654363624735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145947898612136823272665253 27365230989775654363624735)
    ·
      refine ⟨41047846484663481545437103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27365230989775654363624735 41047846484663481545437103)
      ·
        refine ⟨61571769726995222318155655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41047846484663481545437103 61571769726995222318155655)
        ·
          refine ⟨92357654590492833477233483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61571769726995222318155655 92357654590492833477233483)
          ·
            refine ⟨138536481885739250215850225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92357654590492833477233483 138536481885739250215850225)
            ·
              refine ⟨103902361414304437661887669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138536481885739250215850225 103902361414304437661887669)
              ·
                refine ⟨9740846382591041030801969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103902361414304437661887669 9740846382591041030801969)
                ·
                  refine ⟨7305634786943280773101477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9740846382591041030801969 7305634786943280773101477)
                  ·
                    refine ⟨1369806522551865144956527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7305634786943280773101477 1369806522551865144956527)
                    ·
                      rfl

theorem cell22_4001533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_4001533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001533 prefixEnd_4001533 := by exact prefixLift 4001533
  have htrace : WordTrace (prefixWord ++ tailWord_4001533) baseStart_4001533 baseEnd_4001533 := by
    simpa [prefixWord, tailWord_4001533, baseEnd_4001533] using wordTrace_append hprefix tailTrace_4001533
  have hstable : (prefixWord ++ tailWord_4001533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001533).length < 2 ^ (prefixWord ++ tailWord_4001533).sum := by decide
  have hdescent : baseEnd_4001533 < baseStart_4001533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001563 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 7, 3]
def baseStart_4001563 : Nat := 118140960795 + 4001563 * 2 ^ 59
def prefixEnd_4001563 : Nat := 4983230072969 + 3 ^ 40 * 4001563 * 2
def baseEnd_4001563 : Nat := 1369816792164955066706435

theorem tailTrace_4001563 : CollatzResearch.WordTrace tailWord_4001563 prefixEnd_4001563 1369816792164955066706435 := by
  unfold tailWord_4001563
  simp only [CollatzResearch.WordTrace]
  refine ⟨145948992802028138396257343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97299328534685425597504895 145948992802028138396257343)
  ·
    refine ⟨218923489203042207594386015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145948992802028138396257343 218923489203042207594386015)
    ·
      refine ⟨328385233804563311391579023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218923489203042207594386015 328385233804563311391579023)
      ·
        refine ⟨492577850706844967087368535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328385233804563311391579023 492577850706844967087368535)
        ·
          refine ⟨738866776060267450631052803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492577850706844967087368535 738866776060267450631052803)
          ·
            refine ⟨1108300164090401175946579205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738866776060267450631052803 1108300164090401175946579205)
            ·
              refine ⟨207806280766950220489983601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1108300164090401175946579205 207806280766950220489983601)
              ·
                refine ⟨155854710575212665367487701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207806280766950220489983601 155854710575212665367487701)
                ·
                  refine ⟨3652844779106546844550493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 155854710575212665367487701 3652844779106546844550493)
                  ·
                    refine ⟨1369816792164955066706435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3652844779106546844550493 1369816792164955066706435)
                    ·
                      rfl

theorem cell22_4001563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 3].length) (baseStart_4001563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001563 prefixEnd_4001563 := by exact prefixLift 4001563
  have htrace : WordTrace (prefixWord ++ tailWord_4001563) baseStart_4001563 baseEnd_4001563 := by
    simpa [prefixWord, tailWord_4001563, baseEnd_4001563] using wordTrace_append hprefix tailTrace_4001563
  have hstable : (prefixWord ++ tailWord_4001563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001563).length < 2 ^ (prefixWord ++ tailWord_4001563).sum := by decide
  have hdescent : baseEnd_4001563 < baseStart_4001563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001580 : List Nat := [2, 2, 1, 1, 1, 5, 2, 2, 3, 3]
def baseStart_4001580 : Nat := 118140960795 + 4001580 * 2 ^ 59
def prefixEnd_4001580 : Nat := 4983230072969 + 3 ^ 40 * 4001580 * 2
def baseEnd_4001580 : Nat := 1369822611612372689031383

theorem tailTrace_4001580 : CollatzResearch.WordTrace tailWord_4001580 prefixEnd_4001580 1369822611612372689031383 := by
  unfold tailWord_4001580
  simp only [CollatzResearch.WordTrace]
  refine ⟨72974806421483275149813097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97299741895311033533084129 72974806421483275149813097)
  ·
    refine ⟨54731104816112456362359823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72974806421483275149813097 54731104816112456362359823)
    ·
      refine ⟨82096657224168684543539735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54731104816112456362359823 82096657224168684543539735)
      ·
        refine ⟨123144985836253026815309603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82096657224168684543539735 123144985836253026815309603)
        ·
          refine ⟨184717478754379540222964405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123144985836253026815309603 184717478754379540222964405)
          ·
            refine ⟨17317263633223081895902913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184717478754379540222964405 17317263633223081895902913)
            ·
              refine ⟨12987947724917311421927185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17317263633223081895902913 12987947724917311421927185)
              ·
                refine ⟨9740960793687983566445389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12987947724917311421927185 9740960793687983566445389)
                ·
                  refine ⟨3652860297632993837417021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9740960793687983566445389 3652860297632993837417021)
                  ·
                    refine ⟨1369822611612372689031383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3652860297632993837417021 1369822611612372689031383)
                    ·
                      rfl

theorem cell22_4001580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_4001580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001580 prefixEnd_4001580 := by exact prefixLift 4001580
  have htrace : WordTrace (prefixWord ++ tailWord_4001580) baseStart_4001580 baseEnd_4001580 := by
    simpa [prefixWord, tailWord_4001580, baseEnd_4001580] using wordTrace_append hprefix tailTrace_4001580
  have hstable : (prefixWord ++ tailWord_4001580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001580).length < 2 ^ (prefixWord ++ tailWord_4001580).sum := by decide
  have hdescent : baseEnd_4001580 < baseStart_4001580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001640 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 3, 4]
def baseStart_4001640 : Nat := 118140960795 + 4001640 * 2 ^ 59
def prefixEnd_4001640 : Nat := 4983230072969 + 3 ^ 40 * 4001640 * 2
def baseEnd_4001640 : Nat := 1369843150838552532531199

theorem tailTrace_4001640 : CollatzResearch.WordTrace tailWord_4001640 prefixEnd_4001640 1369843150838552532531199 := by
  unfold tailWord_4001640
  simp only [CollatzResearch.WordTrace]
  refine ⟨72975900611374590273405187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97301200815166120364540249 72975900611374590273405187)
  ·
    refine ⟨109463850917061885410107781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72975900611374590273405187 109463850917061885410107781)
    ·
      refine ⟨20524472046949103514395209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109463850917061885410107781 20524472046949103514395209)
      ·
        refine ⟨15393354035211827635796407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20524472046949103514395209 15393354035211827635796407)
        ·
          refine ⟨23090031052817741453694611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15393354035211827635796407 23090031052817741453694611)
          ·
            refine ⟨34635046579226612180541917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23090031052817741453694611 34635046579226612180541917)
            ·
              refine ⟨12988142467209979567703219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34635046579226612180541917 12988142467209979567703219)
              ·
                refine ⟨19482213700814969351554829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12988142467209979567703219 19482213700814969351554829)
                ·
                  refine ⟨7305830137805613506833061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19482213700814969351554829 7305830137805613506833061)
                  ·
                    refine ⟨1369843150838552532531199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7305830137805613506833061 1369843150838552532531199)
                    ·
                      rfl

theorem cell22_4001640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_4001640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001640 prefixEnd_4001640 := by exact prefixLift 4001640
  have htrace : WordTrace (prefixWord ++ tailWord_4001640) baseStart_4001640 baseEnd_4001640 := by
    simpa [prefixWord, tailWord_4001640, baseEnd_4001640] using wordTrace_append hprefix tailTrace_4001640
  have hstable : (prefixWord ++ tailWord_4001640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001640).length < 2 ^ (prefixWord ++ tailWord_4001640).sum := by decide
  have hdescent : baseEnd_4001640 < baseStart_4001640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001657 : List Nat := [1, 2, 1, 3, 2, 2, 5, 1, 1, 4]
def baseStart_4001657 : Nat := 118140960795 + 4001657 * 2 ^ 59
def prefixEnd_4001657 : Nat := 4983230072969 + 3 ^ 40 * 4001657 * 2
def baseEnd_4001657 : Nat := 1369848970285970154856147

theorem tailTrace_4001657 : CollatzResearch.WordTrace tailWord_4001657 prefixEnd_4001657 1369848970285970154856147 := by
  unfold tailWord_4001657
  simp only [CollatzResearch.WordTrace]
  refine ⟨145952421263687592450179225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97301614175791728300119483 145952421263687592450179225)
  ·
    refine ⟨109464315947765694337634419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145952421263687592450179225 109464315947765694337634419)
    ·
      refine ⟨164196473921648541506451629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109464315947765694337634419 164196473921648541506451629)
      ·
        refine ⟨61573677720618203064919361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164196473921648541506451629 61573677720618203064919361)
        ·
          refine ⟨46180258290463652298689521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61573677720618203064919361 46180258290463652298689521)
          ·
            refine ⟨34635193717847739224017141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46180258290463652298689521 34635193717847739224017141)
            ·
              refine ⟨3247049411048225552251607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34635193717847739224017141 3247049411048225552251607)
              ·
                refine ⟨4870574116572338328377411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3247049411048225552251607 4870574116572338328377411)
                ·
                  refine ⟨7305861174858507492566117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4870574116572338328377411 7305861174858507492566117)
                  ·
                    refine ⟨1369848970285970154856147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7305861174858507492566117 1369848970285970154856147)
                    ·
                      rfl

theorem cell22_4001657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 1, 4].length) (baseStart_4001657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001657 prefixEnd_4001657 := by exact prefixLift 4001657
  have htrace : WordTrace (prefixWord ++ tailWord_4001657) baseStart_4001657 baseEnd_4001657 := by
    simpa [prefixWord, tailWord_4001657, baseEnd_4001657] using wordTrace_append hprefix tailTrace_4001657
  have hstable : (prefixWord ++ tailWord_4001657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001657).length < 2 ^ (prefixWord ++ tailWord_4001657).sum := by decide
  have hdescent : baseEnd_4001657 < baseStart_4001657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001665 : List Nat := [1, 2, 4, 4, 2, 1, 2, 2, 1, 3]
def baseStart_4001665 : Nat := 118140960795 + 4001665 * 2 ^ 59
def prefixEnd_4001665 : Nat := 4983230072969 + 3 ^ 40 * 4001665 * 2
def baseEnd_4001665 : Nat := 1369851708849460800656123

theorem tailTrace_4001665 : CollatzResearch.WordTrace tailWord_4001665 prefixEnd_4001665 1369851708849460800656123 := by
  unfold tailWord_4001665
  simp only [CollatzResearch.WordTrace]
  refine ⟨145952713047658609816470449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97301808698439073210980299 145952713047658609816470449)
  ·
    refine ⟨109464534785743957362352837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145952713047658609816470449 109464534785743957362352837)
    ·
      refine ⟨20524600272326992005441157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109464534785743957362352837 20524600272326992005441157)
      ·
        refine ⟨3848362551061311001020217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20524600272326992005441157 3848362551061311001020217)
        ·
          refine ⟨2886271913295983250765163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3848362551061311001020217 2886271913295983250765163)
          ·
            refine ⟨4329407869943974876147745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2886271913295983250765163 4329407869943974876147745)
            ·
              refine ⟨3247055902457981157110809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4329407869943974876147745 3247055902457981157110809)
              ·
                refine ⟨2435291926843485867833107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3247055902457981157110809 2435291926843485867833107)
                ·
                  refine ⟨3652937890265228801749661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435291926843485867833107 3652937890265228801749661)
                  ·
                    refine ⟨1369851708849460800656123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3652937890265228801749661 1369851708849460800656123)
                    ·
                      rfl

theorem cell22_4001665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_4001665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001665 prefixEnd_4001665 := by exact prefixLift 4001665
  have htrace : WordTrace (prefixWord ++ tailWord_4001665) baseStart_4001665 baseEnd_4001665 := by
    simpa [prefixWord, tailWord_4001665, baseEnd_4001665] using wordTrace_append hprefix tailTrace_4001665
  have hstable : (prefixWord ++ tailWord_4001665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001665).length < 2 ^ (prefixWord ++ tailWord_4001665).sum := by decide
  have hdescent : baseEnd_4001665 < baseStart_4001665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001687 : List Nat := [1, 1, 3, 3, 1, 3, 2, 3, 2, 3]
def baseStart_4001687 : Nat := 118140960795 + 4001687 * 2 ^ 59
def prefixEnd_4001687 : Nat := 4983230072969 + 3 ^ 40 * 4001687 * 2
def baseEnd_4001687 : Nat := 1369859239899060076606055

theorem tailTrace_4001687 : CollatzResearch.WordTrace tailWord_4001687 prefixEnd_4001687 1369859239899060076606055 := by
  unfold tailWord_4001687
  simp only [CollatzResearch.WordTrace]
  refine ⟨145953515453578907573771315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97302343635719271715847543 145953515453578907573771315)
  ·
    refine ⟨218930273180368361360656973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145953515453578907573771315 218930273180368361360656973)
    ·
      refine ⟨82098852442638135510246365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218930273180368361360656973 82098852442638135510246365)
      ·
        refine ⟨30787069665989300816342387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82098852442638135510246365 30787069665989300816342387)
        ·
          refine ⟨46180604498983951224513581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30787069665989300816342387 46180604498983951224513581)
          ·
            refine ⟨17317726687118981709192593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46180604498983951224513581 17317726687118981709192593)
            ·
              refine ⟨12988295015339236281894445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17317726687118981709192593 12988295015339236281894445)
              ·
                refine ⟨4870610630752213605710417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12988295015339236281894445 4870610630752213605710417)
                ·
                  refine ⟨3652957973064160204282813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4870610630752213605710417 3652957973064160204282813)
                  ·
                    refine ⟨1369859239899060076606055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3652957973064160204282813 1369859239899060076606055)
                    ·
                      rfl

theorem cell22_4001687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_4001687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001687 prefixEnd_4001687 := by exact prefixLift 4001687
  have htrace : WordTrace (prefixWord ++ tailWord_4001687) baseStart_4001687 baseEnd_4001687 := by
    simpa [prefixWord, tailWord_4001687, baseEnd_4001687] using wordTrace_append hprefix tailTrace_4001687
  have hstable : (prefixWord ++ tailWord_4001687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001687).length < 2 ^ (prefixWord ++ tailWord_4001687).sum := by decide
  have hdescent : baseEnd_4001687 < baseStart_4001687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001715 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 5, 3]
def baseStart_4001715 : Nat := 118140960795 + 4001715 * 2 ^ 59
def prefixEnd_4001715 : Nat := 4983230072969 + 3 ^ 40 * 4001715 * 2
def baseEnd_4001715 : Nat := 1369868824871277336905969

theorem tailTrace_4001715 : CollatzResearch.WordTrace tailWord_4001715 prefixEnd_4001715 1369868824871277336905969 := by
  unfold tailWord_4001715
  simp only [CollatzResearch.WordTrace]
  refine ⟨145954536697477468355790599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97303024464984978903860399 145954536697477468355790599)
  ·
    refine ⟨218931805046216202533685899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145954536697477468355790599 218931805046216202533685899)
    ·
      refine ⟨328397707569324303800528849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218931805046216202533685899 328397707569324303800528849)
      ·
        refine ⟨246298280676993227850396637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328397707569324303800528849 246298280676993227850396637)
        ·
          refine ⟨92361855253872460443898739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246298280676993227850396637 92361855253872460443898739)
          ·
            refine ⟨138542782880808690665848109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92361855253872460443898739 138542782880808690665848109)
            ·
              refine ⟨51953543580303258999693041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138542782880808690665848109 51953543580303258999693041)
              ·
                refine ⟨38965157685227444249769781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51953543580303258999693041 38965157685227444249769781)
                ·
                  refine ⟨3652983532990072898415917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38965157685227444249769781 3652983532990072898415917)
                  ·
                    refine ⟨1369868824871277336905969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3652983532990072898415917 1369868824871277336905969)
                    ·
                      rfl

theorem cell22_4001715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 3].length) (baseStart_4001715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001715 prefixEnd_4001715 := by exact prefixLift 4001715
  have htrace : WordTrace (prefixWord ++ tailWord_4001715) baseStart_4001715 baseEnd_4001715 := by
    simpa [prefixWord, tailWord_4001715, baseEnd_4001715] using wordTrace_append hprefix tailTrace_4001715
  have hstable : (prefixWord ++ tailWord_4001715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001715).length < 2 ^ (prefixWord ++ tailWord_4001715).sum := by decide
  have hdescent : baseEnd_4001715 < baseStart_4001715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001841 : List Nat := [1, 2, 2, 3, 1, 5, 2, 2, 4]
def baseStart_4001841 : Nat := 118140960795 + 4001841 * 2 ^ 59
def prefixEnd_4001841 : Nat := 4983230072969 + 3 ^ 40 * 4001841 * 2
def baseEnd_4001841 : Nat := 456637319082085002751861

theorem tailTrace_4001841 : CollatzResearch.WordTrace tailWord_4001841 prefixEnd_4001841 456637319082085002751861 := by
  unfold tailWord_4001841
  simp only [CollatzResearch.WordTrace]
  refine ⟨145959132295020991874877377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97306088196680661249918251 145959132295020991874877377)
  ·
    refine ⟨109469349221265743906158033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145959132295020991874877377 109469349221265743906158033)
    ·
      refine ⟨82102011915949307929618525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109469349221265743906158033 82102011915949307929618525)
      ·
        refine ⟨30788254468480990473606947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82102011915949307929618525 30788254468480990473606947)
        ·
          refine ⟨46182381702721485710410421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30788254468480990473606947 46182381702721485710410421)
          ·
            refine ⟨4329598284630139285350977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46182381702721485710410421 4329598284630139285350977)
            ·
              refine ⟨3247198713472604464013233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4329598284630139285350977 3247198713472604464013233)
              ·
                refine ⟨2435399035104453348009925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3247198713472604464013233 2435399035104453348009925)
                ·
                  refine ⟨456637319082085002751861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2435399035104453348009925 456637319082085002751861)
                  ·
                    rfl

theorem cell22_4001841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 4].length) (baseStart_4001841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001841 prefixEnd_4001841 := by exact prefixLift 4001841
  have htrace : WordTrace (prefixWord ++ tailWord_4001841) baseStart_4001841 baseEnd_4001841 := by
    simpa [prefixWord, tailWord_4001841, baseEnd_4001841] using wordTrace_append hprefix tailTrace_4001841
  have hstable : (prefixWord ++ tailWord_4001841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001841).length < 2 ^ (prefixWord ++ tailWord_4001841).sum := by decide
  have hdescent : baseEnd_4001841 < baseStart_4001841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001850 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 2, 7]
def baseStart_4001850 : Nat := 118140960795 + 4001850 * 2 ^ 59
def prefixEnd_4001850 : Nat := 4983230072969 + 3 ^ 40 * 4001850 * 2
def baseEnd_4001850 : Nat := 1369915038130181984780555

theorem tailTrace_4001850 : CollatzResearch.WordTrace tailWord_4001850 prefixEnd_4001850 1369915038130181984780555 := by
  unfold tailWord_4001850
  simp only [CollatzResearch.WordTrace]
  refine ⟨36489865137997096602988751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97306307034658924274636669 36489865137997096602988751)
  ·
    refine ⟨54734797706995644904483127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36489865137997096602988751 54734797706995644904483127)
    ·
      refine ⟨82102196560493467356724691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54734797706995644904483127 82102196560493467356724691)
      ·
        refine ⟨123153294840740201035087037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82102196560493467356724691 123153294840740201035087037)
        ·
          refine ⟨46182485565277575388157639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123153294840740201035087037 46182485565277575388157639)
          ·
            refine ⟨69273728347916363082236459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46182485565277575388157639 69273728347916363082236459)
            ·
              refine ⟨103910592521874544623354689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69273728347916363082236459 103910592521874544623354689)
              ·
                refine ⟨77932944391405908467516017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103910592521874544623354689 77932944391405908467516017)
                ·
                  refine ⟨58449708293554431350637013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77932944391405908467516017 58449708293554431350637013)
                  ·
                    refine ⟨1369915038130181984780555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58449708293554431350637013 1369915038130181984780555)
                    ·
                      rfl

theorem cell22_4001850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_4001850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001850 prefixEnd_4001850 := by exact prefixLift 4001850
  have htrace : WordTrace (prefixWord ++ tailWord_4001850) baseStart_4001850 baseEnd_4001850 := by
    simpa [prefixWord, tailWord_4001850, baseEnd_4001850] using wordTrace_append hprefix tailTrace_4001850
  have hstable : (prefixWord ++ tailWord_4001850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001850).length < 2 ^ (prefixWord ++ tailWord_4001850).sum := by decide
  have hdescent : baseEnd_4001850 < baseStart_4001850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001865 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 2, 6]
def baseStart_4001865 : Nat := 118140960795 + 4001865 * 2 ^ 59
def prefixEnd_4001865 : Nat := 4983230072969 + 3 ^ 40 * 4001865 * 2
def baseEnd_4001865 : Nat := 1369920172936726945655509

theorem tailTrace_4001865 : CollatzResearch.WordTrace tailWord_4001865 prefixEnd_4001865 1369920172936726945655509 := by
  unfold tailWord_4001865
  simp only [CollatzResearch.WordTrace]
  refine ⟨145960007646934043973751049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97306671764622695982500699 145960007646934043973751049)
  ·
    refine ⟨109470005735200532980313287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145960007646934043973751049 109470005735200532980313287)
    ·
      refine ⟨164205008602800799470469931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109470005735200532980313287 164205008602800799470469931)
      ·
        refine ⟨246307512904201199205704897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164205008602800799470469931 246307512904201199205704897)
        ·
          refine ⟨184730634678150899404278673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246307512904201199205704897 184730634678150899404278673)
          ·
            refine ⟨138547976008613174553209005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184730634678150899404278673 138547976008613174553209005)
            ·
              refine ⟨51955491003229940457453377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138547976008613174553209005 51955491003229940457453377)
              ·
                refine ⟨38966618252422455343090033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51955491003229940457453377 38966618252422455343090033)
                ·
                  refine ⟨29224963689316841507317525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38966618252422455343090033 29224963689316841507317525)
                  ·
                    refine ⟨1369920172936726945655509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29224963689316841507317525 1369920172936726945655509)
                    ·
                      rfl

theorem cell22_4001865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_4001865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001865 prefixEnd_4001865 := by exact prefixLift 4001865
  have htrace : WordTrace (prefixWord ++ tailWord_4001865) baseStart_4001865 baseEnd_4001865 := by
    simpa [prefixWord, tailWord_4001865, baseEnd_4001865] using wordTrace_append hprefix tailTrace_4001865
  have hstable : (prefixWord ++ tailWord_4001865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001865).length < 2 ^ (prefixWord ++ tailWord_4001865).sum := by decide
  have hdescent : baseEnd_4001865 < baseStart_4001865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001867 : List Nat := [1, 1, 1, 1, 3, 1, 2, 6, 3, 3]
def baseStart_4001867 : Nat := 118140960795 + 4001867 * 2 ^ 59
def prefixEnd_4001867 : Nat := 4983230072969 + 3 ^ 40 * 4001867 * 2
def baseEnd_4001867 : Nat := 1369920857577599607105503

theorem tailTrace_4001867 : CollatzResearch.WordTrace tailWord_4001867 prefixEnd_4001867 1369920857577599607105503 := by
  unfold tailWord_4001867
  simp only [CollatzResearch.WordTrace]
  refine ⟨145960080592926798315323855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97306720395284532210215903 145960080592926798315323855)
  ·
    refine ⟨218940120889390197472985783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145960080592926798315323855 218940120889390197472985783)
    ·
      refine ⟨328410181334085296209478675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218940120889390197472985783 328410181334085296209478675)
      ·
        refine ⟨492615272001127944314218013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328410181334085296209478675 492615272001127944314218013)
        ·
          refine ⟨184730727000422979117831755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 492615272001127944314218013 184730727000422979117831755)
          ·
            refine ⟨277096090500634468676747633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184730727000422979117831755 277096090500634468676747633)
            ·
              refine ⟨207822067875475851507560725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277096090500634468676747633 207822067875475851507560725)
              ·
                refine ⟨9741659431662930539416909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207822067875475851507560725 9741659431662930539416909)
                ·
                  refine ⟨3653122286873598952281341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9741659431662930539416909 3653122286873598952281341)
                  ·
                    refine ⟨1369920857577599607105503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3653122286873598952281341 1369920857577599607105503)
                    ·
                      rfl

theorem cell22_4001867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 3].length) (baseStart_4001867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001867 prefixEnd_4001867 := by exact prefixLift 4001867
  have htrace : WordTrace (prefixWord ++ tailWord_4001867) baseStart_4001867 baseEnd_4001867 := by
    simpa [prefixWord, tailWord_4001867, baseEnd_4001867] using wordTrace_append hprefix tailTrace_4001867
  have hstable : (prefixWord ++ tailWord_4001867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001867).length < 2 ^ (prefixWord ++ tailWord_4001867).sum := by decide
  have hdescent : baseEnd_4001867 < baseStart_4001867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001869 : List Nat := [1, 6, 1, 1, 1, 1, 5, 6]
def baseStart_4001869 : Nat := 118140960795 + 4001869 * 2 ^ 59
def prefixEnd_4001869 : Nat := 4983230072969 + 3 ^ 40 * 4001869 * 2
def baseEnd_4001869 : Nat := 152213504690941363172833

theorem tailTrace_4001869 : CollatzResearch.WordTrace tailWord_4001869 prefixEnd_4001869 152213504690941363172833 := by
  unfold tailWord_4001869
  simp only [CollatzResearch.WordTrace]
  refine ⟨145960153538919552656896661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97306769025946368437931107 145960153538919552656896661)
  ·
    refine ⟨6841882197136854030792031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145960153538919552656896661 6841882197136854030792031)
    ·
      refine ⟨10262823295705281046188047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6841882197136854030792031 10262823295705281046188047)
      ·
        refine ⟨15394234943557921569282071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10262823295705281046188047 15394234943557921569282071)
        ·
          refine ⟨23091352415336882353923107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15394234943557921569282071 23091352415336882353923107)
          ·
            refine ⟨34637028623005323530884661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23091352415336882353923107 34637028623005323530884661)
            ·
              refine ⟨3247221433406749081020437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34637028623005323530884661 3247221433406749081020437)
              ·
                refine ⟨152213504690941363172833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3247221433406749081020437 152213504690941363172833)
                ·
                  rfl

theorem cell22_4001869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 6].length) (baseStart_4001869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001869 prefixEnd_4001869 := by exact prefixLift 4001869
  have htrace : WordTrace (prefixWord ++ tailWord_4001869) baseStart_4001869 baseEnd_4001869 := by
    simpa [prefixWord, tailWord_4001869, baseEnd_4001869] using wordTrace_append hprefix tailTrace_4001869
  have hstable : (prefixWord ++ tailWord_4001869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001869).length < 2 ^ (prefixWord ++ tailWord_4001869).sum := by decide
  have hdescent : baseEnd_4001869 < baseStart_4001869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001886 : List Nat := [4, 4, 1, 1, 2, 1, 9]
def baseStart_4001886 : Nat := 118140960795 + 4001886 * 2 ^ 59
def prefixEnd_4001886 : Nat := 4983230072969 + 3 ^ 40 * 4001886 * 2
def baseEnd_4001886 : Nat := 50738050432069995958535

theorem tailTrace_4001886 : CollatzResearch.WordTrace tailWord_4001886 prefixEnd_4001886 50738050432069995958535 := by
  unfold tailWord_4001886
  simp only [CollatzResearch.WordTrace]
  refine ⟨18245096697482245570033189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97307182386571976373510341 18245096697482245570033189)
  ·
    refine ⟨3420955630777921044381223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18245096697482245570033189 3420955630777921044381223)
    ·
      refine ⟨5131433446166881566571835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3420955630777921044381223 5131433446166881566571835)
      ·
        refine ⟨7697150169250322349857753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5131433446166881566571835 7697150169250322349857753)
        ·
          refine ⟨5772862626937741762393315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7697150169250322349857753 5772862626937741762393315)
          ·
            refine ⟨8659293940406612643589973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5772862626937741762393315 8659293940406612643589973)
            ·
              refine ⟨50738050432069995958535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8659293940406612643589973 50738050432069995958535)
              ·
                rfl

theorem cell22_4001886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 9].length) (baseStart_4001886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001886 prefixEnd_4001886 := by exact prefixLift 4001886
  have htrace : WordTrace (prefixWord ++ tailWord_4001886) baseStart_4001886 baseEnd_4001886 := by
    simpa [prefixWord, tailWord_4001886, baseEnd_4001886] using wordTrace_append hprefix tailTrace_4001886
  have hstable : (prefixWord ++ tailWord_4001886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001886).length < 2 ^ (prefixWord ++ tailWord_4001886).sum := by decide
  have hdescent : baseEnd_4001886 < baseStart_4001886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001890 : List Nat := [3, 3, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_4001890 : Nat := 118140960795 + 4001890 * 2 ^ 59
def prefixEnd_4001890 : Nat := 4983230072969 + 3 ^ 40 * 4001890 * 2
def baseEnd_4001890 : Nat := 1369928730947635213780433

theorem tailTrace_4001890 : CollatzResearch.WordTrace tailWord_4001890 prefixEnd_4001890 1369928730947635213780433 := by
  unfold tailWord_4001890
  simp only [CollatzResearch.WordTrace]
  refine ⟨36490229867960868310852781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97307279647895648828940749 36490229867960868310852781)
  ·
    refine ⟨13683836200485325616569793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36490229867960868310852781 13683836200485325616569793)
    ·
      refine ⟨10262877150363994212427345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13683836200485325616569793 10262877150363994212427345)
      ·
        refine ⟨7697157862772995659320509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10262877150363994212427345 7697157862772995659320509)
        ·
          refine ⟨2886434198539873372245191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7697157862772995659320509 2886434198539873372245191)
          ·
            refine ⟨4329651297809810058367787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2886434198539873372245191 4329651297809810058367787)
            ·
              refine ⟨6494476946714715087551681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4329651297809810058367787 6494476946714715087551681)
              ·
                refine ⟨4870857710036036315663761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6494476946714715087551681 4870857710036036315663761)
                ·
                  refine ⟨3653143282527027236747821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4870857710036036315663761 3653143282527027236747821)
                  ·
                    refine ⟨1369928730947635213780433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3653143282527027236747821 1369928730947635213780433)
                    ·
                      rfl

theorem cell22_4001890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_4001890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001890 prefixEnd_4001890 := by exact prefixLift 4001890
  have htrace : WordTrace (prefixWord ++ tailWord_4001890) baseStart_4001890 baseEnd_4001890 := by
    simpa [prefixWord, tailWord_4001890, baseEnd_4001890] using wordTrace_append hprefix tailTrace_4001890
  have hstable : (prefixWord ++ tailWord_4001890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001890).length < 2 ^ (prefixWord ++ tailWord_4001890).sum := by decide
  have hdescent : baseEnd_4001890 < baseStart_4001890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001901 : List Nat := [1, 5, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_4001901 : Nat := 118140960795 + 4001901 * 2 ^ 59
def prefixEnd_4001901 : Nat := 4983230072969 + 3 ^ 40 * 4001901 * 2
def baseEnd_4001901 : Nat := 1369932496472434851755399

theorem tailTrace_4001901 : CollatzResearch.WordTrace tailWord_4001901 prefixEnd_4001901 1369932496472434851755399 := by
  unfold tailWord_4001901
  simp only [CollatzResearch.WordTrace]
  refine ⟨145961320674803622122061557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97307547116535748081374371 145961320674803622122061557)
  ·
    refine ⟨13683873813262839573943271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145961320674803622122061557 13683873813262839573943271)
    ·
      refine ⟨20525810719894259360914907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13683873813262839573943271 20525810719894259360914907)
      ·
        refine ⟨30788716079841389041372361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20525810719894259360914907 30788716079841389041372361)
        ·
          refine ⟨23091537059881041781029271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30788716079841389041372361 23091537059881041781029271)
          ·
            refine ⟨34637305589821562671543907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23091537059881041781029271 34637305589821562671543907)
            ·
              refine ⟨51955958384732344007315861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34637305589821562671543907 51955958384732344007315861)
              ·
                refine ⟨2435435549284328625342931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51955958384732344007315861 2435435549284328625342931)
                ·
                  refine ⟨3653153323926492938014397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435435549284328625342931 3653153323926492938014397)
                  ·
                    refine ⟨1369932496472434851755399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3653153323926492938014397 1369932496472434851755399)
                    ·
                      rfl

theorem cell22_4001901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_4001901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001901 prefixEnd_4001901 := by exact prefixLift 4001901
  have htrace : WordTrace (prefixWord ++ tailWord_4001901) baseStart_4001901 baseEnd_4001901 := by
    simpa [prefixWord, tailWord_4001901, baseEnd_4001901] using wordTrace_append hprefix tailTrace_4001901
  have hstable : (prefixWord ++ tailWord_4001901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001901).length < 2 ^ (prefixWord ++ tailWord_4001901).sum := by decide
  have hdescent : baseEnd_4001901 < baseStart_4001901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001927 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 3, 4]
def baseStart_4001927 : Nat := 118140960795 + 4001927 * 2 ^ 59
def prefixEnd_4001927 : Nat := 4983230072969 + 3 ^ 40 * 4001927 * 2
def baseEnd_4001927 : Nat := 1369941396803779450605319

theorem tailTrace_4001927 : CollatzResearch.WordTrace tailWord_4001927 prefixEnd_4001927 1369941396803779450605319 := by
  unfold tailWord_4001927
  simp only [CollatzResearch.WordTrace]
  refine ⟨145962268972709428562508035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97308179315139619041672023 145962268972709428562508035)
  ·
    refine ⟨218943403459064142843762053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145962268972709428562508035 218943403459064142843762053)
    ·
      refine ⟨41051888148574526783205385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218943403459064142843762053 41051888148574526783205385)
      ·
        refine ⟨30788916111430895087404039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41051888148574526783205385 30788916111430895087404039)
        ·
          refine ⟨46183374167146342631106059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30788916111430895087404039 46183374167146342631106059)
          ·
            refine ⟨69275061250719513946659089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46183374167146342631106059 69275061250719513946659089)
            ·
              refine ⟨51956295938039635459994317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69275061250719513946659089 51956295938039635459994317)
              ·
                refine ⟨19483610976764863297497869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51956295938039635459994317 19483610976764863297497869)
                ·
                  refine ⟨7306354116286823736561701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19483610976764863297497869 7306354116286823736561701)
                  ·
                    refine ⟨1369941396803779450605319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7306354116286823736561701 1369941396803779450605319)
                    ·
                      rfl

theorem cell22_4001927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_4001927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001927 prefixEnd_4001927 := by exact prefixLift 4001927
  have htrace : WordTrace (prefixWord ++ tailWord_4001927) baseStart_4001927 baseEnd_4001927 := by
    simpa [prefixWord, tailWord_4001927, baseEnd_4001927] using wordTrace_append hprefix tailTrace_4001927
  have hstable : (prefixWord ++ tailWord_4001927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001927).length < 2 ^ (prefixWord ++ tailWord_4001927).sum := by decide
  have hdescent : baseEnd_4001927 < baseStart_4001927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002017 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 1, 8]
def baseStart_4002017 : Nat := 118140960795 + 4002017 * 2 ^ 59
def prefixEnd_4002017 : Nat := 4983230072969 + 3 ^ 40 * 4002017 * 2
def baseEnd_4002017 : Nat := 1369972205643049215855043

theorem tailTrace_4002017 : CollatzResearch.WordTrace tailWord_4002017 prefixEnd_4002017 1369972205643049215855043 := by
  unfold tailWord_4002017
  simp only [CollatzResearch.WordTrace]
  refine ⟨145965551542383373933284305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97310367694922249288856203 145965551542383373933284305)
  ·
    refine ⟨109474163656787530449963229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145965551542383373933284305 109474163656787530449963229)
    ·
      refine ⟨41052811371295323918736211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109474163656787530449963229 41052811371295323918736211)
      ·
        refine ⟨61579217056942985878104317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41052811371295323918736211 61579217056942985878104317)
        ·
          refine ⟨23092206396353619704289119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61579217056942985878104317 23092206396353619704289119)
          ·
            refine ⟨34638309594530429556433679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23092206396353619704289119 34638309594530429556433679)
            ·
              refine ⟨51957464391795644334650519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34638309594530429556433679 51957464391795644334650519)
              ·
                refine ⟨77936196587693466501975779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51957464391795644334650519 77936196587693466501975779)
                ·
                  refine ⟨116904294881540199752963669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77936196587693466501975779 116904294881540199752963669)
                  ·
                    refine ⟨1369972205643049215855043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116904294881540199752963669 1369972205643049215855043)
                    ·
                      rfl

theorem cell22_4002017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_4002017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4002017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4002017 prefixEnd_4002017 := by exact prefixLift 4002017
  have htrace : WordTrace (prefixWord ++ tailWord_4002017) baseStart_4002017 baseEnd_4002017 := by
    simpa [prefixWord, tailWord_4002017, baseEnd_4002017] using wordTrace_append hprefix tailTrace_4002017
  have hstable : (prefixWord ++ tailWord_4002017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002017).length < 2 ^ (prefixWord ++ tailWord_4002017).sum := by decide
  have hdescent : baseEnd_4002017 < baseStart_4002017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002047 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 1, 7]
def baseStart_4002047 : Nat := 118140960795 + 4002047 * 2 ^ 59
def prefixEnd_4002047 : Nat := 4983230072969 + 3 ^ 40 * 4002047 * 2
def baseEnd_4002047 : Nat := 1369982475256139137604951

theorem tailTrace_4002047 : CollatzResearch.WordTrace tailWord_4002047 prefixEnd_4002047 1369982475256139137604951 := by
  unfold tailWord_4002047
  simp only [CollatzResearch.WordTrace]
  refine ⟨145966645732274689056876395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97311097154849792704584263 145966645732274689056876395)
  ·
    refine ⟨218949968598412033585314593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145966645732274689056876395 218949968598412033585314593)
    ·
      refine ⟨164212476448809025188985945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218949968598412033585314593 164212476448809025188985945)
      ·
        refine ⟨123159357336606768891739459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164212476448809025188985945 123159357336606768891739459)
        ·
          refine ⟨184739036004910153337609189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123159357336606768891739459 184739036004910153337609189)
          ·
            refine ⟨34638569250920653750801723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184739036004910153337609189 34638569250920653750801723)
            ·
              refine ⟨51957853876380980626202585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34638569250920653750801723 51957853876380980626202585)
              ·
                refine ⟨38968390407285735469651939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51957853876380980626202585 38968390407285735469651939)
                ·
                  refine ⟨58452585610928603204477909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38968390407285735469651939 58452585610928603204477909)
                  ·
                    refine ⟨1369982475256139137604951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58452585610928603204477909 1369982475256139137604951)
                    ·
                      rfl

theorem cell22_4002047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_4002047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4002047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4002047 prefixEnd_4002047 := by exact prefixLift 4002047
  have htrace : WordTrace (prefixWord ++ tailWord_4002047) baseStart_4002047 baseEnd_4002047 := by
    simpa [prefixWord, tailWord_4002047, baseEnd_4002047] using wordTrace_append hprefix tailTrace_4002047
  have hstable : (prefixWord ++ tailWord_4002047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002047).length < 2 ^ (prefixWord ++ tailWord_4002047).sum := by decide
  have hdescent : baseEnd_4002047 < baseStart_4002047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002128 : List Nat := [2, 1, 1, 1, 1, 7, 3, 2, 4]
def baseStart_4002128 : Nat := 118140960795 + 4002128 * 2 ^ 59
def prefixEnd_4002128 : Nat := 4983230072969 + 3 ^ 40 * 4002128 * 2
def baseEnd_4002128 : Nat := 456670067737160642109901

theorem tailTrace_4002128 : CollatzResearch.WordTrace tailWord_4002128 prefixEnd_4002128 456670067737160642109901 := by
  unfold tailWord_4002128
  simp only [CollatzResearch.WordTrace]
  refine ⟨72984800022490619945287519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97313066696654159927050025 72984800022490619945287519)
  ·
    refine ⟨109477200033735929917931279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72984800022490619945287519 109477200033735929917931279)
    ·
      refine ⟨164215800050603894876896919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109477200033735929917931279 164215800050603894876896919)
      ·
        refine ⟨246323700075905842315345379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164215800050603894876896919 246323700075905842315345379)
        ·
          refine ⟨369485550113858763473018069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246323700075905842315345379 369485550113858763473018069)
          ·
            refine ⟨8659817580793564768898861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 369485550113858763473018069 8659817580793564768898861)
            ·
              refine ⟨3247431592797586788337073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8659817580793564768898861 3247431592797586788337073)
              ·
                refine ⟨2435573694598190091252805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3247431592797586788337073 2435573694598190091252805)
                ·
                  refine ⟨456670067737160642109901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2435573694598190091252805 456670067737160642109901)
                  ·
                    rfl

theorem cell22_4002128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 4].length) (baseStart_4002128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4002128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4002128 prefixEnd_4002128 := by exact prefixLift 4002128
  have htrace : WordTrace (prefixWord ++ tailWord_4002128) baseStart_4002128 baseEnd_4002128 := by
    simpa [prefixWord, tailWord_4002128, baseEnd_4002128] using wordTrace_append hprefix tailTrace_4002128
  have hstable : (prefixWord ++ tailWord_4002128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002128).length < 2 ^ (prefixWord ++ tailWord_4002128).sum := by decide
  have hdescent : baseEnd_4002128 < baseStart_4002128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002143 : List Nat := [1, 1, 2, 3, 1, 2, 6, 1, 2, 3]
def baseStart_4002143 : Nat := 118140960795 + 4002143 * 2 ^ 59
def prefixEnd_4002143 : Nat := 4983230072969 + 3 ^ 40 * 4002143 * 2
def baseEnd_4002143 : Nat := 1370015338018026887204657

theorem tailTrace_4002143 : CollatzResearch.WordTrace tailWord_4002143 prefixEnd_4002143 1370015338018026887204657 := by
  unfold tailWord_4002143
  simp only [CollatzResearch.WordTrace]
  refine ⟨145970147139926897452371083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97313431426617931634914055 145970147139926897452371083)
  ·
    refine ⟨218955220709890346178556625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145970147139926897452371083 218955220709890346178556625)
    ·
      refine ⟨164216415532417759633917469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218955220709890346178556625 164216415532417759633917469)
      ·
        refine ⟨61581155824656659862719051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164216415532417759633917469 61581155824656659862719051)
        ·
          refine ⟨92371733736984989794078577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61581155824656659862719051 92371733736984989794078577)
          ·
            refine ⟨69278800302738742345558933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92371733736984989794078577 69278800302738742345558933)
            ·
              refine ⟨3247443764190878547448075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69278800302738742345558933 3247443764190878547448075)
              ·
                refine ⟨4871165646286317821172113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3247443764190878547448075 4871165646286317821172113)
                ·
                  refine ⟨3653374234714738365879085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4871165646286317821172113 3653374234714738365879085)
                  ·
                    refine ⟨1370015338018026887204657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3653374234714738365879085 1370015338018026887204657)
                    ·
                      rfl

theorem cell22_4002143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 2, 3].length) (baseStart_4002143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4002143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4002143 prefixEnd_4002143 := by exact prefixLift 4002143
  have htrace : WordTrace (prefixWord ++ tailWord_4002143) baseStart_4002143 baseEnd_4002143 := by
    simpa [prefixWord, tailWord_4002143, baseEnd_4002143] using wordTrace_append hprefix tailTrace_4002143
  have hstable : (prefixWord ++ tailWord_4002143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002143).length < 2 ^ (prefixWord ++ tailWord_4002143).sum := by decide
  have hdescent : baseEnd_4002143 < baseStart_4002143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002199 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 1, 7]
def baseStart_4002199 : Nat := 118140960795 + 4002199 * 2 ^ 59
def prefixEnd_4002199 : Nat := 4983230072969 + 3 ^ 40 * 4002199 * 2
def baseEnd_4002199 : Nat := 1370034507962461407804485

theorem tailTrace_4002199 : CollatzResearch.WordTrace tailWord_4002199 prefixEnd_4002199 1370034507962461407804485 := by
  unfold tailWord_4002199
  simp only [CollatzResearch.WordTrace]
  refine ⟨145972189627724019016409651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97314793085149346010939767 145972189627724019016409651)
  ·
    refine ⟨218958284441586028524614477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145972189627724019016409651 218958284441586028524614477)
    ·
      refine ⟨82109356665594760696730429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218958284441586028524614477 82109356665594760696730429)
      ·
        refine ⟨30791008749598035261273911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82109356665594760696730429 30791008749598035261273911)
        ·
          refine ⟨46186513124397052891910867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30791008749598035261273911 46186513124397052891910867)
          ·
            refine ⟨69279769686595579337866301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46186513124397052891910867 69279769686595579337866301)
            ·
              refine ⟨25979913632473342251699863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69279769686595579337866301 25979913632473342251699863)
              ·
                refine ⟨38969870448710013377549795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25979913632473342251699863 38969870448710013377549795)
                ·
                  refine ⟨58454805673065020066324693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38969870448710013377549795 58454805673065020066324693)
                  ·
                    refine ⟨1370034507962461407804485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58454805673065020066324693 1370034507962461407804485)
                    ·
                      rfl

theorem cell22_4002199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_4002199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4002199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4002199 prefixEnd_4002199 := by exact prefixLift 4002199
  have htrace : WordTrace (prefixWord ++ tailWord_4002199) baseStart_4002199 baseEnd_4002199 := by
    simpa [prefixWord, tailWord_4002199, baseEnd_4002199] using wordTrace_append hprefix tailTrace_4002199
  have hstable : (prefixWord ++ tailWord_4002199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002199).length < 2 ^ (prefixWord ++ tailWord_4002199).sum := by decide
  have hdescent : baseEnd_4002199 < baseStart_4002199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002280 : List Nat := [2, 1, 4, 1, 1, 5, 1, 3, 4]
def baseStart_4002280 : Nat := 118140960795 + 4002280 * 2 ^ 59
def prefixEnd_4002280 : Nat := 4983230072969 + 3 ^ 40 * 4002280 * 2
def baseEnd_4002280 : Nat := 456687411972601398843079

theorem tailTrace_4002280 : CollatzResearch.WordTrace tailWord_4002280 prefixEnd_4002280 456687411972601398843079 := by
  unfold tailWord_4002280
  simp only [CollatzResearch.WordTrace]
  refine ⟨72987571970215284925054147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97316762626953713233405529 72987571970215284925054147)
  ·
    refine ⟨109481357955322927387581221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72987571970215284925054147 109481357955322927387581221)
    ·
      refine ⟨20527754616623048885171479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109481357955322927387581221 20527754616623048885171479)
      ·
        refine ⟨30791631924934573327757219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20527754616623048885171479 30791631924934573327757219)
        ·
          refine ⟨46187447887401859991635829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30791631924934573327757219 46187447887401859991635829)
          ·
            refine ⟨4330073239443924374215859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46187447887401859991635829 4330073239443924374215859)
            ·
              refine ⟨6495109859165886561323789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4330073239443924374215859 6495109859165886561323789)
              ·
                refine ⟨2435666197187207460496421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6495109859165886561323789 2435666197187207460496421)
                ·
                  refine ⟨456687411972601398843079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2435666197187207460496421 456687411972601398843079)
                  ·
                    rfl

theorem cell22_4002280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 4].length) (baseStart_4002280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4002280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4002280 prefixEnd_4002280 := by exact prefixLift 4002280
  have htrace : WordTrace (prefixWord ++ tailWord_4002280) baseStart_4002280 baseEnd_4002280 := by
    simpa [prefixWord, tailWord_4002280, baseEnd_4002280] using wordTrace_append hprefix tailTrace_4002280
  have hstable : (prefixWord ++ tailWord_4002280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002280).length < 2 ^ (prefixWord ++ tailWord_4002280).sum := by decide
  have hdescent : baseEnd_4002280 < baseStart_4002280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002308 : List Nat := [2, 3, 2, 3, 1, 2, 2, 7]
def baseStart_4002308 : Nat := 118140960795 + 4002308 * 2 ^ 59
def prefixEnd_4002308 : Nat := 4983230072969 + 3 ^ 40 * 4002308 * 2
def baseEnd_4002308 : Nat := 152230202321113495203239

theorem tailTrace_4002308 : CollatzResearch.WordTrace tailWord_4002308 prefixEnd_4002308 152230202321113495203239 := by
  unfold tailWord_4002308
  simp only [CollatzResearch.WordTrace]
  refine ⟨72988082592164565316063789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97317443456219420421418385 72988082592164565316063789)
  ·
    refine ⟨27370530972061711993523921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72988082592164565316063789 27370530972061711993523921)
    ·
      refine ⟨20527898229046283995142941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27370530972061711993523921 20527898229046283995142941)
      ·
        refine ⟨7697961835892356498178603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20527898229046283995142941 7697961835892356498178603)
        ·
          refine ⟨11546942753838534747267905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7697961835892356498178603 11546942753838534747267905)
          ·
            refine ⟨8660207065378901060450929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11546942753838534747267905 8660207065378901060450929)
            ·
              refine ⟨6495155299034175795338197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8660207065378901060450929 6495155299034175795338197)
              ·
                refine ⟨152230202321113495203239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6495155299034175795338197 152230202321113495203239)
                ·
                  rfl

theorem cell22_4002308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 7].length) (baseStart_4002308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4002308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4002308 prefixEnd_4002308 := by exact prefixLift 4002308
  have htrace : WordTrace (prefixWord ++ tailWord_4002308) baseStart_4002308 baseEnd_4002308 := by
    simpa [prefixWord, tailWord_4002308, baseEnd_4002308] using wordTrace_append hprefix tailTrace_4002308
  have hstable : (prefixWord ++ tailWord_4002308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002308).length < 2 ^ (prefixWord ++ tailWord_4002308).sum := by decide
  have hdescent : baseEnd_4002308 < baseStart_4002308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002400 : List Nat := [2, 1, 1, 3, 2, 1, 6, 1, 1, 4]
def baseStart_4002400 : Nat := 118140960795 + 4002400 * 2 ^ 59
def prefixEnd_4002400 : Nat := 4983230072969 + 3 ^ 40 * 4002400 * 2
def baseEnd_4002400 : Nat := 1370103314370163883528869

theorem tailTrace_4002400 : CollatzResearch.WordTrace tailWord_4002400 prefixEnd_4002400 1370103314370163883528869 := by
  unfold tailWord_4002400
  simp only [CollatzResearch.WordTrace]
  refine ⟨72989760349997915172238327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97319680466663886896317769 72989760349997915172238327)
  ·
    refine ⟨109484640524996872758357491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72989760349997915172238327 109484640524996872758357491)
    ·
      refine ⟨164226960787495309137536237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109484640524996872758357491 164226960787495309137536237)
      ·
        refine ⟨61585110295310740926576089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164226960787495309137536237 61585110295310740926576089)
        ·
          refine ⟨46188832721483055694932067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61585110295310740926576089 46188832721483055694932067)
          ·
            refine ⟨69283249082224583542398101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46188832721483055694932067 69283249082224583542398101)
            ·
              refine ⟨3247652300729277353549911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69283249082224583542398101 3247652300729277353549911)
              ·
                refine ⟨4871478451093916030324867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3247652300729277353549911 4871478451093916030324867)
                ·
                  refine ⟨7307217676640874045487301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4871478451093916030324867 7307217676640874045487301)
                  ·
                    refine ⟨1370103314370163883528869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7307217676640874045487301 1370103314370163883528869)
                    ·
                      rfl

theorem cell22_4002400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 1, 4].length) (baseStart_4002400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4002400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4002400 prefixEnd_4002400 := by exact prefixLift 4002400
  have htrace : WordTrace (prefixWord ++ tailWord_4002400) baseStart_4002400 baseEnd_4002400 := by
    simpa [prefixWord, tailWord_4002400, baseEnd_4002400] using wordTrace_append hprefix tailTrace_4002400
  have hstable : (prefixWord ++ tailWord_4002400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002400).length < 2 ^ (prefixWord ++ tailWord_4002400).sum := by decide
  have hdescent : baseEnd_4002400 < baseStart_4002400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002441 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 1, 9]
def baseStart_4002441 : Nat := 118140960795 + 4002441 * 2 ^ 59
def prefixEnd_4002441 : Nat := 4983230072969 + 3 ^ 40 * 4002441 * 2
def baseEnd_4002441 : Nat := 1370117349508053443253743

theorem tailTrace_4002441 : CollatzResearch.WordTrace tailWord_4002441 prefixEnd_4002441 1370117349508053443253743 := by
  unfold tailWord_4002441
  simp only [CollatzResearch.WordTrace]
  refine ⟨145981016092847294346719177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97320677395231529564479451 145981016092847294346719177)
  ·
    refine ⟨109485762069635470760039383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145981016092847294346719177 109485762069635470760039383)
    ·
      refine ⟨164228643104453206140059075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109485762069635470760039383 164228643104453206140059075)
      ·
        refine ⟨246342964656679809210088613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164228643104453206140059075 246342964656679809210088613)
        ·
          refine ⟨46189305873127464226891615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246342964656679809210088613 46189305873127464226891615)
          ·
            refine ⟨69283958809691196340337423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46189305873127464226891615 69283958809691196340337423)
            ·
              refine ⟨103925938214536794510506135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69283958809691196340337423 103925938214536794510506135)
              ·
                refine ⟨155888907321805191765759203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103925938214536794510506135 155888907321805191765759203)
                ·
                  refine ⟨233833360982707787648638805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155888907321805191765759203 233833360982707787648638805)
                  ·
                    refine ⟨1370117349508053443253743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 233833360982707787648638805 1370117349508053443253743)
                    ·
                      rfl

theorem cell22_4002441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_4002441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4002441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4002441 prefixEnd_4002441 := by exact prefixLift 4002441
  have htrace : WordTrace (prefixWord ++ tailWord_4002441) baseStart_4002441 baseEnd_4002441 := by
    simpa [prefixWord, tailWord_4002441, baseEnd_4002441] using wordTrace_append hprefix tailTrace_4002441
  have hstable : (prefixWord ++ tailWord_4002441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002441).length < 2 ^ (prefixWord ++ tailWord_4002441).sum := by decide
  have hdescent : baseEnd_4002441 < baseStart_4002441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002481 : List Nat := [1, 2, 2, 6, 1, 2, 2, 1, 2, 3]
def baseStart_4002481 : Nat := 118140960795 + 4002481 * 2 ^ 59
def prefixEnd_4002481 : Nat := 4983230072969 + 3 ^ 40 * 4002481 * 2
def baseEnd_4002481 : Nat := 1370131042325506672253621

theorem tailTrace_4002481 : CollatzResearch.WordTrace tailWord_4002481 prefixEnd_4002481 1370131042325506672253621 := by
  unfold tailWord_4002481
  simp only [CollatzResearch.WordTrace]
  refine ⟨145982475012702381178175297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97321650008468254118783531 145982475012702381178175297)
  ·
    refine ⟨109486856259526785883631473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145982475012702381178175297 109486856259526785883631473)
    ·
      refine ⟨82115142194645089412723605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109486856259526785883631473 82115142194645089412723605)
      ·
        refine ⟨3849147290373988566221419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82115142194645089412723605 3849147290373988566221419)
        ·
          refine ⟨5773720935560982849332129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3849147290373988566221419 5773720935560982849332129)
          ·
            refine ⟨4330290701670737136999097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5773720935560982849332129 4330290701670737136999097)
            ·
              refine ⟨3247718026253052852749323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4330290701670737136999097 3247718026253052852749323)
              ·
                refine ⟨4871577039379579279123985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3247718026253052852749323 4871577039379579279123985)
                ·
                  refine ⟨3653682779534684459342989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4871577039379579279123985 3653682779534684459342989)
                  ·
                    refine ⟨1370131042325506672253621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3653682779534684459342989 1370131042325506672253621)
                    ·
                      rfl

theorem cell22_4002481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 2, 3].length) (baseStart_4002481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4002481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4002481 prefixEnd_4002481 := by exact prefixLift 4002481
  have htrace : WordTrace (prefixWord ++ tailWord_4002481) baseStart_4002481 baseEnd_4002481 := by
    simpa [prefixWord, tailWord_4002481, baseEnd_4002481] using wordTrace_append hprefix tailTrace_4002481
  have hstable : (prefixWord ++ tailWord_4002481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002481).length < 2 ^ (prefixWord ++ tailWord_4002481).sum := by decide
  have hdescent : baseEnd_4002481 < baseStart_4002481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002550 : List Nat := [5, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_4002550 : Nat := 118140960795 + 4002550 * 2 ^ 59
def prefixEnd_4002550 : Nat := 4983230072969 + 3 ^ 40 * 4002550 * 2
def baseEnd_4002550 : Nat := 456718220811871164092803

theorem tailTrace_4002550 : CollatzResearch.WordTrace tailWord_4002550 prefixEnd_4002550 456718220811871164092803 := by
  unfold tailWord_4002550
  simp only [CollatzResearch.WordTrace]
  refine ⟨9124061978090775372652319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97323327766301603974958069 9124061978090775372652319)
  ·
    refine ⟨13686092967136163058978479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9124061978090775372652319 13686092967136163058978479)
    ·
      refine ⟨20529139450704244588467719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13686092967136163058978479 20529139450704244588467719)
      ·
        refine ⟨30793709176056366882701579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20529139450704244588467719 30793709176056366882701579)
        ·
          refine ⟨46190563764084550324052369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30793709176056366882701579 46190563764084550324052369)
          ·
            refine ⟨34642922823063412743039277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46190563764084550324052369 34642922823063412743039277)
            ·
              refine ⟨12991096058648779778639729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34642922823063412743039277 12991096058648779778639729)
              ·
                refine ⟨9743322043986584833979797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12991096058648779778639729 9743322043986584833979797)
                ·
                  refine ⟨456718220811871164092803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9743322043986584833979797 456718220811871164092803)
                  ·
                    rfl

theorem cell22_4002550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_4002550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4002550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4002550 prefixEnd_4002550 := by exact prefixLift 4002550
  have htrace : WordTrace (prefixWord ++ tailWord_4002550) baseStart_4002550 baseEnd_4002550 := by
    simpa [prefixWord, tailWord_4002550, baseEnd_4002550] using wordTrace_append hprefix tailTrace_4002550
  have hstable : (prefixWord ++ tailWord_4002550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002550).length < 2 ^ (prefixWord ++ tailWord_4002550).sum := by decide
  have hdescent : baseEnd_4002550 < baseStart_4002550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002567 : List Nat := [1, 1, 4, 4, 1, 1, 1, 5, 4]
def baseStart_4002567 : Nat := 118140960795 + 4002567 * 2 ^ 59
def prefixEnd_4002567 : Nat := 4983230072969 + 3 ^ 40 * 4002567 * 2
def baseEnd_4002567 : Nat := 456720160627677038201119

theorem tailTrace_4002567 : CollatzResearch.WordTrace tailWord_4002567 prefixEnd_4002567 456720160627677038201119 := by
  unfold tailWord_4002567
  simp only [CollatzResearch.WordTrace]
  refine ⟨145985611690390817865805955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97323741126927211910537303 145985611690390817865805955)
  ·
    refine ⟨218978417535586226798708933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145985611690390817865805955 218978417535586226798708933)
    ·
      refine ⟨41058453287922417524757925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218978417535586226798708933 41058453287922417524757925)
      ·
        refine ⟨7698459991485453285892111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41058453287922417524757925 7698459991485453285892111)
        ·
          refine ⟨11547689987228179928838167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7698459991485453285892111 11547689987228179928838167)
          ·
            refine ⟨17321534980842269893257251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11547689987228179928838167 17321534980842269893257251)
            ·
              refine ⟨25982302471263404839885877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17321534980842269893257251 25982302471263404839885877)
              ·
                refine ⟨2435840856680944203739301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25982302471263404839885877 2435840856680944203739301)
                ·
                  refine ⟨456720160627677038201119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2435840856680944203739301 456720160627677038201119)
                  ·
                    rfl

theorem cell22_4002567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 4].length) (baseStart_4002567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4002567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4002567 prefixEnd_4002567 := by exact prefixLift 4002567
  have htrace : WordTrace (prefixWord ++ tailWord_4002567) baseStart_4002567 baseEnd_4002567 := by
    simpa [prefixWord, tailWord_4002567, baseEnd_4002567] using wordTrace_append hprefix tailTrace_4002567
  have hstable : (prefixWord ++ tailWord_4002567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002567).length < 2 ^ (prefixWord ++ tailWord_4002567).sum := by decide
  have hdescent : baseEnd_4002567 < baseStart_4002567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002608 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 2, 6]
def baseStart_4002608 : Nat := 118140960795 + 4002608 * 2 ^ 59
def prefixEnd_4002608 : Nat := 4983230072969 + 3 ^ 40 * 4002608 * 2
def baseEnd_4002608 : Nat := 1370174517020920674328231

theorem tailTrace_4002608 : CollatzResearch.WordTrace tailWord_4002608 prefixEnd_4002608 1370174517020920674328231 := by
  unfold tailWord_4002608
  simp only [CollatzResearch.WordTrace]
  refine ⟨72993553541621140934024239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97324738055494854578698985 72993553541621140934024239)
  ·
    refine ⟨109490330312431711401036359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72993553541621140934024239 109490330312431711401036359)
    ·
      refine ⟨164235495468647567101554539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109490330312431711401036359 164235495468647567101554539)
      ·
        refine ⟨246353243202971350652331809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164235495468647567101554539 246353243202971350652331809)
        ·
          refine ⟨184764932402228512989248857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246353243202971350652331809 184764932402228512989248857)
          ·
            refine ⟨138573699301671384741936643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184764932402228512989248857 138573699301671384741936643)
            ·
              refine ⟨207860548952507077112904965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138573699301671384741936643 207860548952507077112904965)
              ·
                refine ⟨38973852928595076958669681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207860548952507077112904965 38973852928595076958669681)
                ·
                  refine ⟨29230389696446307719002261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38973852928595076958669681 29230389696446307719002261)
                  ·
                    refine ⟨1370174517020920674328231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29230389696446307719002261 1370174517020920674328231)
                    ·
                      rfl

theorem cell22_4002608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_4002608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4002608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4002608 prefixEnd_4002608 := by exact prefixLift 4002608
  have htrace : WordTrace (prefixWord ++ tailWord_4002608) baseStart_4002608 baseEnd_4002608 := by
    simpa [prefixWord, tailWord_4002608, baseEnd_4002608] using wordTrace_append hprefix tailTrace_4002608
  have hstable : (prefixWord ++ tailWord_4002608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002608).length < 2 ^ (prefixWord ++ tailWord_4002608).sum := by decide
  have hdescent : baseEnd_4002608 < baseStart_4002608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002612 : List Nat := [2, 5, 1, 1, 3, 1, 1, 8]
def baseStart_4002612 : Nat := 118140960795 + 4002612 * 2 ^ 59
def prefixEnd_4002612 : Nat := 4983230072969 + 3 ^ 40 * 4002612 * 2
def baseEnd_4002612 : Nat := 152241765144740666358691

theorem tailTrace_4002612 : CollatzResearch.WordTrace tailWord_4002612 prefixEnd_4002612 152241765144740666358691 := by
  unfold tailWord_4002612
  simp only [CollatzResearch.WordTrace]
  refine ⟨72993626487613895275597045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97324835316818527034129393 72993626487613895275597045)
  ·
    refine ⟨6843152483213802682087223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72993626487613895275597045 6843152483213802682087223)
    ·
      refine ⟨10264728724820704023130835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6843152483213802682087223 10264728724820704023130835)
      ·
        refine ⟨15397093087231056034696253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10264728724820704023130835 15397093087231056034696253)
        ·
          refine ⟨5773909907711646013011095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15397093087231056034696253 5773909907711646013011095)
          ·
            refine ⟨8660864861567469019516643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5773909907711646013011095 8660864861567469019516643)
            ·
              refine ⟨12991297292351203529274965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8660864861567469019516643 12991297292351203529274965)
              ·
                refine ⟨152241765144740666358691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12991297292351203529274965 152241765144740666358691)
                ·
                  rfl

theorem cell22_4002612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 8].length) (baseStart_4002612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4002612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4002612 prefixEnd_4002612 := by exact prefixLift 4002612
  have htrace : WordTrace (prefixWord ++ tailWord_4002612) baseStart_4002612 baseEnd_4002612 := by
    simpa [prefixWord, tailWord_4002612, baseEnd_4002612] using wordTrace_append hprefix tailTrace_4002612
  have hstable : (prefixWord ++ tailWord_4002612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002612).length < 2 ^ (prefixWord ++ tailWord_4002612).sum := by decide
  have hdescent : baseEnd_4002612 < baseStart_4002612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002717 : List Nat := [1, 4, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_4002717 : Nat := 118140960795 + 4002717 * 2 ^ 59
def prefixEnd_4002717 : Nat := 4983230072969 + 3 ^ 40 * 4002717 * 2
def baseEnd_4002717 : Nat := 1370211829948480723352897

theorem tailTrace_4002717 : CollatzResearch.WordTrace tailWord_4002717 prefixEnd_4002717 1370211829948480723352897 := by
  unfold tailWord_4002717
  simp only [CollatzResearch.WordTrace]
  refine ⟨145991082639847393483766405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97327388426564928989177603 145991082639847393483766405)
  ·
    refine ⟨27373327994971386278206201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145991082639847393483766405 27373327994971386278206201)
    ·
      refine ⟨20529995996228539708654651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27373327994971386278206201 20529995996228539708654651)
      ·
        refine ⟨30794993994342809562981977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20529995996228539708654651 30794993994342809562981977)
        ·
          refine ⟨23096245495757107172236483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30794993994342809562981977 23096245495757107172236483)
          ·
            refine ⟨34644368243635660758354725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23096245495757107172236483 34644368243635660758354725)
            ·
              refine ⟨6495819045681686392191511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34644368243635660758354725 6495819045681686392191511)
              ·
                refine ⟨9743728568522529588287267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6495819045681686392191511 9743728568522529588287267)
                ·
                  refine ⟨14615592852783794382430901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9743728568522529588287267 14615592852783794382430901)
                  ·
                    refine ⟨1370211829948480723352897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14615592852783794382430901 1370211829948480723352897)
                    ·
                      rfl

theorem cell22_4002717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_4002717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4002717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4002717 prefixEnd_4002717 := by exact prefixLift 4002717
  have htrace : WordTrace (prefixWord ++ tailWord_4002717) baseStart_4002717 baseEnd_4002717 := by
    simpa [prefixWord, tailWord_4002717, baseEnd_4002717] using wordTrace_append hprefix tailTrace_4002717
  have hstable : (prefixWord ++ tailWord_4002717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002717).length < 2 ^ (prefixWord ++ tailWord_4002717).sum := by decide
  have hdescent : baseEnd_4002717 < baseStart_4002717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002826 : List Nat := [3, 1, 2, 2, 3, 3, 2, 1, 5]
def baseStart_4002826 : Nat := 118140960795 + 4002826 * 2 ^ 59
def prefixEnd_4002826 : Nat := 4983230072969 + 3 ^ 40 * 4002826 * 2
def baseEnd_4002826 : Nat := 456749714292013590792521

theorem tailTrace_4002826 : CollatzResearch.WordTrace tailWord_4002826 prefixEnd_4002826 456749714292013590792521 := by
  unfold tailWord_4002826
  simp only [CollatzResearch.WordTrace]
  refine ⟨36498764549113126274871083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97330038797635003399656221 36498764549113126274871083)
  ·
    refine ⟨54748146823669689412306625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36498764549113126274871083 54748146823669689412306625)
    ·
      refine ⟨41061110117752267059229969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54748146823669689412306625 41061110117752267059229969)
      ·
        refine ⟨30795832588314200294422477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41061110117752267059229969 30795832588314200294422477)
        ·
          refine ⟨11548437220617825110408429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30795832588314200294422477 11548437220617825110408429)
          ·
            refine ⟨4330663957731684416403161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11548437220617825110408429 4330663957731684416403161)
            ·
              refine ⟨3247997968298763312302371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4330663957731684416403161 3247997968298763312302371)
              ·
                refine ⟨4871996952448144968453557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3247997968298763312302371 4871996952448144968453557)
                ·
                  refine ⟨456749714292013590792521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4871996952448144968453557 456749714292013590792521)
                  ·
                    rfl

theorem cell22_4002826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_4002826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4002826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4002826 prefixEnd_4002826 := by exact prefixLift 4002826
  have htrace : WordTrace (prefixWord ++ tailWord_4002826) baseStart_4002826 baseEnd_4002826 := by
    simpa [prefixWord, tailWord_4002826, baseEnd_4002826] using wordTrace_append hprefix tailTrace_4002826
  have hstable : (prefixWord ++ tailWord_4002826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002826).length < 2 ^ (prefixWord ++ tailWord_4002826).sum := by decide
  have hdescent : baseEnd_4002826 < baseStart_4002826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002839 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 3, 4]
def baseStart_4002839 : Nat := 118140960795 + 4002839 * 2 ^ 59
def prefixEnd_4002839 : Nat := 4983230072969 + 3 ^ 40 * 4002839 * 2
def baseEnd_4002839 : Nat := 1370253593041713071802523

theorem tailTrace_4002839 : CollatzResearch.WordTrace tailWord_4002839 prefixEnd_4002839 1370253593041713071802523 := by
  unfold tailWord_4002839
  simp only [CollatzResearch.WordTrace]
  refine ⟨145995532345405408319707571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97330354896936938879805047 145995532345405408319707571)
  ·
    refine ⟨218993298518108112479561357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145995532345405408319707571 218993298518108112479561357)
    ·
      refine ⟨82122486944290542179835509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218993298518108112479561357 82122486944290542179835509)
      ·
        refine ⟨7698983151027238329359579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82122486944290542179835509 7698983151027238329359579)
        ·
          refine ⟨11548474726540857494039369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7698983151027238329359579 11548474726540857494039369)
          ·
            refine ⟨8661356044905643120529527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11548474726540857494039369 8661356044905643120529527)
            ·
              refine ⟨12992034067358464680794291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8661356044905643120529527 12992034067358464680794291)
              ·
                refine ⟨19488051101037697021191437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12992034067358464680794291 19488051101037697021191437)
                ·
                  refine ⟨7308019162889136382946789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19488051101037697021191437 7308019162889136382946789)
                  ·
                    refine ⟨1370253593041713071802523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7308019162889136382946789 1370253593041713071802523)
                    ·
                      rfl

theorem cell22_4002839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_4002839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4002839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4002839 prefixEnd_4002839 := by exact prefixLift 4002839
  have htrace : WordTrace (prefixWord ++ tailWord_4002839) baseStart_4002839 baseEnd_4002839 := by
    simpa [prefixWord, tailWord_4002839, baseEnd_4002839] using wordTrace_append hprefix tailTrace_4002839
  have hstable : (prefixWord ++ tailWord_4002839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002839).length < 2 ^ (prefixWord ++ tailWord_4002839).sum := by decide
  have hdescent : baseEnd_4002839 < baseStart_4002839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002886 : List Nat := [6, 1, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_4002886 : Nat := 118140960795 + 4002886 * 2 ^ 59
def prefixEnd_4002886 : Nat := 4983230072969 + 3 ^ 40 * 4002886 * 2
def baseEnd_4002886 : Nat := 1370269682102220615877379

theorem tailTrace_4002886 : CollatzResearch.WordTrace tailWord_4002886 prefixEnd_4002886 1370269682102220615877379 := by
  unfold tailWord_4002886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4562413955507347979583391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97331497717490090231112341 4562413955507347979583391)
  ·
    refine ⟨6843620933261021969375087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4562413955507347979583391 6843620933261021969375087)
    ·
      refine ⟨10265431399891532954062631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6843620933261021969375087 10265431399891532954062631)
      ·
        refine ⟨15398147099837299431093947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10265431399891532954062631 15398147099837299431093947)
        ·
          refine ⟨23097220649755949146640921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15398147099837299431093947 23097220649755949146640921)
          ·
            refine ⟨17322915487316961859980691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23097220649755949146640921 17322915487316961859980691)
            ·
              refine ⟨25984373230975442789971037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17322915487316961859980691 25984373230975442789971037)
              ·
                refine ⟨9744139961615791046239139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25984373230975442789971037 9744139961615791046239139)
                ·
                  refine ⟨14616209942423686569358709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9744139961615791046239139 14616209942423686569358709)
                  ·
                    refine ⟨1370269682102220615877379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14616209942423686569358709 1370269682102220615877379)
                    ·
                      rfl

theorem cell22_4002886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_4002886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4002886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4002886 prefixEnd_4002886 := by exact prefixLift 4002886
  have htrace : WordTrace (prefixWord ++ tailWord_4002886) baseStart_4002886 baseEnd_4002886 := by
    simpa [prefixWord, tailWord_4002886, baseEnd_4002886] using wordTrace_append hprefix tailTrace_4002886
  have hstable : (prefixWord ++ tailWord_4002886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002886).length < 2 ^ (prefixWord ++ tailWord_4002886).sum := by decide
  have hdescent : baseEnd_4002886 < baseStart_4002886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002920 : List Nat := [2, 1, 4, 4, 1, 2, 1, 2, 2, 3]
def baseStart_4002920 : Nat := 118140960795 + 4002920 * 2 ^ 59
def prefixEnd_4002920 : Nat := 4983230072969 + 3 ^ 40 * 4002920 * 2
def baseEnd_4002920 : Nat := 1370281320997055860527275

theorem tailTrace_4002920 : CollatzResearch.WordTrace tailWord_4002920 prefixEnd_4002920 1370281320997055860527275 := by
  unfold tailWord_4002920
  simp only [CollatzResearch.WordTrace]
  refine ⟨72999243329055979576703107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97332324438741306102270809 72999243329055979576703107)
  ·
    refine ⟨109498864993583969365054661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72999243329055979576703107 109498864993583969365054661)
    ·
      refine ⟨20531037186296994255947749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109498864993583969365054661 20531037186296994255947749)
      ·
        refine ⟨3849569472430686422990203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20531037186296994255947749 3849569472430686422990203)
        ·
          refine ⟨5774354208646029634485305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3849569472430686422990203 5774354208646029634485305)
          ·
            refine ⟨4330765656484522225863979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5774354208646029634485305 4330765656484522225863979)
            ·
              refine ⟨6496148484726783338795969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4330765656484522225863979 6496148484726783338795969)
              ·
                refine ⟨4872111363545087504096977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6496148484726783338795969 4872111363545087504096977)
                ·
                  refine ⟨3654083522658815628072733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4872111363545087504096977 3654083522658815628072733)
                  ·
                    refine ⟨1370281320997055860527275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3654083522658815628072733 1370281320997055860527275)
                    ·
                      rfl

theorem cell22_4002920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_4002920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4002920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4002920 prefixEnd_4002920 := by exact prefixLift 4002920
  have htrace : WordTrace (prefixWord ++ tailWord_4002920) baseStart_4002920 baseEnd_4002920 := by
    simpa [prefixWord, tailWord_4002920, baseEnd_4002920] using wordTrace_append hprefix tailTrace_4002920
  have hstable : (prefixWord ++ tailWord_4002920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002920).length < 2 ^ (prefixWord ++ tailWord_4002920).sum := by decide
  have hdescent : baseEnd_4002920 < baseStart_4002920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002927 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 7]
def baseStart_4002927 : Nat := 118140960795 + 4002927 * 2 ^ 59
def prefixEnd_4002927 : Nat := 4983230072969 + 3 ^ 40 * 4002927 * 2
def baseEnd_4002927 : Nat := 456761239080036725200751

theorem tailTrace_4002927 : CollatzResearch.WordTrace tailWord_4002927 prefixEnd_4002927 456761239080036725200751 := by
  unfold tailWord_4002927
  simp only [CollatzResearch.WordTrace]
  refine ⟨145998741969086599348911035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97332494646057732899274023 145998741969086599348911035)
  ·
    refine ⟨218998112953629899023366553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145998741969086599348911035 218998112953629899023366553)
    ·
      refine ⟨164248584715222424267524915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218998112953629899023366553 164248584715222424267524915)
      ·
        refine ⟨246372877072833636401287373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164248584715222424267524915 246372877072833636401287373)
        ·
          refine ⟨92389828902312613650482765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246372877072833636401287373 92389828902312613650482765)
          ·
            refine ⟨34646185838367230118931037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92389828902312613650482765 34646185838367230118931037)
            ·
              refine ⟨12992319689387711294599139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34646185838367230118931037 12992319689387711294599139)
              ·
                refine ⟨19488479534081566941898709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12992319689387711294599139 19488479534081566941898709)
                ·
                  refine ⟨456761239080036725200751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19488479534081566941898709 456761239080036725200751)
                  ·
                    rfl

theorem cell22_4002927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 7].length) (baseStart_4002927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4002927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4002927 prefixEnd_4002927 := by exact prefixLift 4002927
  have htrace : WordTrace (prefixWord ++ tailWord_4002927) baseStart_4002927 baseEnd_4002927 := by
    simpa [prefixWord, tailWord_4002927, baseEnd_4002927] using wordTrace_append hprefix tailTrace_4002927
  have hstable : (prefixWord ++ tailWord_4002927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002927).length < 2 ^ (prefixWord ++ tailWord_4002927).sum := by decide
  have hdescent : baseEnd_4002927 < baseStart_4002927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003008 : List Nat := [2, 1, 1, 2, 6, 2, 1, 2, 1, 4]
def baseStart_4003008 : Nat := 118140960795 + 4003008 * 2 ^ 59
def prefixEnd_4003008 : Nat := 4983230072969 + 3 ^ 40 * 4003008 * 2
def baseEnd_4003008 : Nat := 1370311445195452964327005

theorem tailTrace_4003008 : CollatzResearch.WordTrace tailWord_4003008 prefixEnd_4003008 1370311445195452964327005 := by
  unfold tailWord_4003008
  simp only [CollatzResearch.WordTrace]
  refine ⟨73000848140896575091304839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97334464187862100121739785 73000848140896575091304839)
  ·
    refine ⟨109501272211344862636957259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73000848140896575091304839 109501272211344862636957259)
    ·
      refine ⟨164251908317017293955435889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109501272211344862636957259 164251908317017293955435889)
      ·
        refine ⟨123188931237762970466576917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164251908317017293955435889 123188931237762970466576917)
        ·
          refine ⟨5774481151770139240620793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123188931237762970466576917 5774481151770139240620793)
          ·
            refine ⟨4330860863827604430465595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5774481151770139240620793 4330860863827604430465595)
            ·
              refine ⟨6496291295741406645698393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4330860863827604430465595 6496291295741406645698393)
              ·
                refine ⟨4872218471806054984273795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6496291295741406645698393 4872218471806054984273795)
                ·
                  refine ⟨7308327707709082476410693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4872218471806054984273795 7308327707709082476410693)
                  ·
                    refine ⟨1370311445195452964327005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7308327707709082476410693 1370311445195452964327005)
                    ·
                      rfl

theorem cell22_4003008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 1, 4].length) (baseStart_4003008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003008 prefixEnd_4003008 := by exact prefixLift 4003008
  have htrace : WordTrace (prefixWord ++ tailWord_4003008) baseStart_4003008 baseEnd_4003008 := by
    simpa [prefixWord, tailWord_4003008, baseEnd_4003008] using wordTrace_append hprefix tailTrace_4003008
  have hstable : (prefixWord ++ tailWord_4003008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003008).length < 2 ^ (prefixWord ++ tailWord_4003008).sum := by decide
  have hdescent : baseEnd_4003008 < baseStart_4003008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003066 : List Nat := [3, 1, 1, 1, 1, 4, 3, 2, 3, 3]
def baseStart_4003066 : Nat := 118140960795 + 4003066 * 2 ^ 59
def prefixEnd_4003066 : Nat := 4983230072969 + 3 ^ 40 * 4003066 * 2
def baseEnd_4003066 : Nat := 1370331299780760146376827

theorem tailTrace_4003066 : CollatzResearch.WordTrace tailWord_4003066 prefixEnd_4003066 1370331299780760146376827 := by
  unfold tailWord_4003066
  simp only [CollatzResearch.WordTrace]
  refine ⟨36500952928895756522055263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97335874477055350725480701 36500952928895756522055263)
  ·
    refine ⟨54751429393343634783082895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36500952928895756522055263 54751429393343634783082895)
    ·
      refine ⟨82127144090015452174624343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54751429393343634783082895 82127144090015452174624343)
      ·
        refine ⟨123190716135023178261936515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82127144090015452174624343 123190716135023178261936515)
        ·
          refine ⟨184786074202534767392904773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123190716135023178261936515 184786074202534767392904773)
          ·
            refine ⟨34647388912975268886169645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184786074202534767392904773 34647388912975268886169645)
            ·
              refine ⟨12992770842365725832313617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34647388912975268886169645 12992770842365725832313617)
              ·
                refine ⟨9744578131774294374235213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12992770842365725832313617 9744578131774294374235213)
                ·
                  refine ⟨3654216799415360390338205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9744578131774294374235213 3654216799415360390338205)
                  ·
                    refine ⟨1370331299780760146376827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3654216799415360390338205 1370331299780760146376827)
                    ·
                      rfl

theorem cell22_4003066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_4003066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003066 prefixEnd_4003066 := by exact prefixLift 4003066
  have htrace : WordTrace (prefixWord ++ tailWord_4003066) baseStart_4003066 baseEnd_4003066 := by
    simpa [prefixWord, tailWord_4003066, baseEnd_4003066] using wordTrace_append hprefix tailTrace_4003066
  have hstable : (prefixWord ++ tailWord_4003066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003066).length < 2 ^ (prefixWord ++ tailWord_4003066).sum := by decide
  have hdescent : baseEnd_4003066 < baseStart_4003066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003083 : List Nat := [1, 1, 1, 1, 5, 3, 1, 5, 1, 3]
def baseStart_4003083 : Nat := 118140960795 + 4003083 * 2 ^ 59
def prefixEnd_4003083 : Nat := 4983230072969 + 3 ^ 40 * 4003083 * 2
def baseEnd_4003083 : Nat := 1370337119228177768701775

theorem tailTrace_4003083 : CollatzResearch.WordTrace tailWord_4003083 prefixEnd_4003083 1370337119228177768701775 := by
  unfold tailWord_4003083
  simp only [CollatzResearch.WordTrace]
  refine ⟨146004431756521437991589903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97336287837680958661059935 146004431756521437991589903)
  ·
    refine ⟨219006647634782156987384855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146004431756521437991589903 219006647634782156987384855)
    ·
      refine ⟨328509971452173235481077283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219006647634782156987384855 328509971452173235481077283)
      ·
        refine ⟨492764957178259853221615925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328509971452173235481077283 492764957178259853221615925)
        ·
          refine ⟨46196714735461861239526493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 492764957178259853221615925 46196714735461861239526493)
          ·
            refine ⟨17323768025798197964822435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46196714735461861239526493 17323768025798197964822435)
            ·
              refine ⟨25985652038697296947233653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17323768025798197964822435 25985652038697296947233653)
              ·
                refine ⟨2436154878627871588803155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25985652038697296947233653 2436154878627871588803155)
                ·
                  refine ⟨3654232317941807383204733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2436154878627871588803155 3654232317941807383204733)
                  ·
                    refine ⟨1370337119228177768701775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3654232317941807383204733 1370337119228177768701775)
                    ·
                      rfl

theorem cell22_4003083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 1, 3].length) (baseStart_4003083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003083 prefixEnd_4003083 := by exact prefixLift 4003083
  have htrace : WordTrace (prefixWord ++ tailWord_4003083) baseStart_4003083 baseEnd_4003083 := by
    simpa [prefixWord, tailWord_4003083, baseEnd_4003083] using wordTrace_append hprefix tailTrace_4003083
  have hstable : (prefixWord ++ tailWord_4003083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003083).length < 2 ^ (prefixWord ++ tailWord_4003083).sum := by decide
  have hdescent : baseEnd_4003083 < baseStart_4003083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003096 : List Nat := [2, 1, 2, 3, 1, 3, 3, 2, 5]
def baseStart_4003096 : Nat := 118140960795 + 4003096 * 2 ^ 59
def prefixEnd_4003096 : Nat := 4983230072969 + 3 ^ 40 * 4003096 * 2
def baseEnd_4003096 : Nat := 456780523131283356042245

theorem tailTrace_4003096 : CollatzResearch.WordTrace tailWord_4003096 prefixEnd_4003096 456780523131283356042245 := by
  unfold tailWord_4003096
  simp only [CollatzResearch.WordTrace]
  refine ⟨73002452952737170605906571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97336603936982894141208761 73002452952737170605906571)
  ·
    refine ⟨109503679429105755908859857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73002452952737170605906571 109503679429105755908859857)
    ·
      refine ⟨82127759571829316931644893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109503679429105755908859857 82127759571829316931644893)
      ·
        refine ⟨30797909839435993849366835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82127759571829316931644893 30797909839435993849366835)
        ·
          refine ⟨46196864759153990774050253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30797909839435993849366835 46196864759153990774050253)
          ·
            refine ⟨17323824284682746540268845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46196864759153990774050253 17323824284682746540268845)
            ·
              refine ⟨6496434106756029952600817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17323824284682746540268845 6496434106756029952600817)
              ·
                refine ⟨4872325580067022464450613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6496434106756029952600817 4872325580067022464450613)
                ·
                  refine ⟨456780523131283356042245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4872325580067022464450613 456780523131283356042245)
                  ·
                    rfl

theorem cell22_4003096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 5].length) (baseStart_4003096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003096 prefixEnd_4003096 := by exact prefixLift 4003096
  have htrace : WordTrace (prefixWord ++ tailWord_4003096) baseStart_4003096 baseEnd_4003096 := by
    simpa [prefixWord, tailWord_4003096, baseEnd_4003096] using wordTrace_append hprefix tailTrace_4003096
  have hstable : (prefixWord ++ tailWord_4003096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003096).length < 2 ^ (prefixWord ++ tailWord_4003096).sum := by decide
  have hdescent : baseEnd_4003096 < baseStart_4003096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003139 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 3, 5]
def baseStart_4003139 : Nat := 118140960795 + 4003139 * 2 ^ 59
def prefixEnd_4003139 : Nat := 4983230072969 + 3 ^ 40 * 4003139 * 2
def baseEnd_4003139 : Nat := 1370356289172612289301603

theorem tailTrace_4003139 : CollatzResearch.WordTrace tailWord_4003139 prefixEnd_4003139 1370356289172612289301603 := by
  unfold tailWord_4003139
  simp only [CollatzResearch.WordTrace]
  refine ⟨146006474244318559555628471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97337649496212373037085647 146006474244318559555628471)
  ·
    refine ⟨219009711366477839333442707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146006474244318559555628471 219009711366477839333442707)
    ·
      refine ⟨328514567049716759000164061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219009711366477839333442707 328514567049716759000164061)
      ·
        refine ⟨123192962643643784625061523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328514567049716759000164061 123192962643643784625061523)
        ·
          refine ⟨184789443965465676937592285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123192962643643784625061523 184789443965465676937592285)
          ·
            refine ⟨69296041487049628851597107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184789443965465676937592285 69296041487049628851597107)
            ·
              refine ⟨103944062230574443277395661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69296041487049628851597107 103944062230574443277395661)
              ·
                refine ⟨38979023336465416229023373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103944062230574443277395661 38979023336465416229023373)
                ·
                  refine ⟨14617133751174531085883765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38979023336465416229023373 14617133751174531085883765)
                  ·
                    refine ⟨1370356289172612289301603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14617133751174531085883765 1370356289172612289301603)
                    ·
                      rfl

theorem cell22_4003139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 5].length) (baseStart_4003139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003139 prefixEnd_4003139 := by exact prefixLift 4003139
  have htrace : WordTrace (prefixWord ++ tailWord_4003139) baseStart_4003139 baseEnd_4003139 := by
    simpa [prefixWord, tailWord_4003139, baseEnd_4003139] using wordTrace_append hprefix tailTrace_4003139
  have hstable : (prefixWord ++ tailWord_4003139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003139).length < 2 ^ (prefixWord ++ tailWord_4003139).sum := by decide
  have hdescent : baseEnd_4003139 < baseStart_4003139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003173 : List Nat := [1, 3, 1, 3, 1, 2, 3, 3, 2, 3]
def baseStart_4003173 : Nat := 118140960795 + 4003173 * 2 ^ 59
def prefixEnd_4003173 : Nat := 4983230072969 + 3 ^ 40 * 4003173 * 2
def baseEnd_4003173 : Nat := 1370367928067447533951499

theorem tailTrace_4003173 : CollatzResearch.WordTrace tailWord_4003173 prefixEnd_4003173 1370367928067447533951499 := by
  unfold tailWord_4003173
  simp only [CollatzResearch.WordTrace]
  refine ⟨146007714326195383362366173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97338476217463588908244115 146007714326195383362366173)
  ·
    refine ⟨54752892872323268760887315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146007714326195383362366173 54752892872323268760887315)
    ·
      refine ⟨82129339308484903141330973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54752892872323268760887315 82129339308484903141330973)
      ·
        refine ⟨30798502240681838677999115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82129339308484903141330973 30798502240681838677999115)
        ·
          refine ⟨46197753361022758016998673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30798502240681838677999115 46197753361022758016998673)
          ·
            refine ⟨34648315020767068512749005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46197753361022758016998673 34648315020767068512749005)
            ·
              refine ⟨12993118132787650692280877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34648315020767068512749005 12993118132787650692280877)
              ·
                refine ⟨4872419299795369009605329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12993118132787650692280877 4872419299795369009605329)
                ·
                  refine ⟨3654314474846526757203997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4872419299795369009605329 3654314474846526757203997)
                  ·
                    refine ⟨1370367928067447533951499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3654314474846526757203997 1370367928067447533951499)
                    ·
                      rfl

theorem cell22_4003173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_4003173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003173 prefixEnd_4003173 := by exact prefixLift 4003173
  have htrace : WordTrace (prefixWord ++ tailWord_4003173) baseStart_4003173 baseEnd_4003173 := by
    simpa [prefixWord, tailWord_4003173, baseEnd_4003173] using wordTrace_append hprefix tailTrace_4003173
  have hstable : (prefixWord ++ tailWord_4003173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003173).length < 2 ^ (prefixWord ++ tailWord_4003173).sum := by decide
  have hdescent : baseEnd_4003173 < baseStart_4003173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003199 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 3, 8]
def baseStart_4003199 : Nat := 118140960795 + 4003199 * 2 ^ 59
def prefixEnd_4003199 : Nat := 4983230072969 + 3 ^ 40 * 4003199 * 2
def baseEnd_4003199 : Nat := 1370376828398792132801419

theorem tailTrace_4003199 : CollatzResearch.WordTrace tailWord_4003199 prefixEnd_4003199 1370376828398792132801419 := by
  unfold tailWord_4003199
  simp only [CollatzResearch.WordTrace]
  refine ⟨146008662624101189802812651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97339108416067459868541767 146008662624101189802812651)
  ·
    refine ⟨219012993936151784704218977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146008662624101189802812651 219012993936151784704218977)
    ·
      refine ⟨164259745452113838528164233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219012993936151784704218977 164259745452113838528164233)
      ·
        refine ⟨123194809089085378896123175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164259745452113838528164233 123194809089085378896123175)
        ·
          refine ⟨184792213633628068344184763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123194809089085378896123175 184792213633628068344184763)
          ·
            refine ⟨277188320450442102516277145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184792213633628068344184763 277188320450442102516277145)
            ·
              refine ⟨207891240337831576887207859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277188320450442102516277145 207891240337831576887207859)
              ·
                refine ⟨311836860506747365330811789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207891240337831576887207859 311836860506747365330811789)
                ·
                  refine ⟨116938822690030261999054421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311836860506747365330811789 116938822690030261999054421)
                  ·
                    refine ⟨1370376828398792132801419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116938822690030261999054421 1370376828398792132801419)
                    ·
                      rfl

theorem cell22_4003199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_4003199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003199 prefixEnd_4003199 := by exact prefixLift 4003199
  have htrace : WordTrace (prefixWord ++ tailWord_4003199) baseStart_4003199 baseEnd_4003199 := by
    simpa [prefixWord, tailWord_4003199, baseEnd_4003199] using wordTrace_append hprefix tailTrace_4003199
  have hstable : (prefixWord ++ tailWord_4003199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003199).length < 2 ^ (prefixWord ++ tailWord_4003199).sum := by decide
  have hdescent : baseEnd_4003199 < baseStart_4003199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003293 : List Nat := [1, 4, 3, 1, 1, 2, 2, 2, 6]
def baseStart_4003293 : Nat := 118140960795 + 4003293 * 2 ^ 59
def prefixEnd_4003293 : Nat := 4983230072969 + 3 ^ 40 * 4003293 * 2
def baseEnd_4003293 : Nat := 456803002173269073650377

theorem tailTrace_4003293 : CollatzResearch.WordTrace tailWord_4003293 prefixEnd_4003293 456803002173269073650377 := by
  unfold tailWord_4003293
  simp only [CollatzResearch.WordTrace]
  refine ⟨146012091085760643856734533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97341394057173762571156355 146012091085760643856734533)
  ·
    refine ⟨27377267078580120723137725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146012091085760643856734533 27377267078580120723137725)
    ·
      refine ⟨10266475154467545271176647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27377267078580120723137725 10266475154467545271176647)
      ·
        refine ⟨15399712731701317906764971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10266475154467545271176647 15399712731701317906764971)
        ·
          refine ⟨23099569097551976860147457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15399712731701317906764971 23099569097551976860147457)
          ·
            refine ⟨17324676823163982645110593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23099569097551976860147457 17324676823163982645110593)
            ·
              refine ⟨12993507617372986983832945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17324676823163982645110593 12993507617372986983832945)
              ·
                refine ⟨9745130713029740237874709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12993507617372986983832945 9745130713029740237874709)
                ·
                  refine ⟨456803002173269073650377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9745130713029740237874709 456803002173269073650377)
                  ·
                    rfl

theorem cell22_4003293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_4003293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003293 prefixEnd_4003293 := by exact prefixLift 4003293
  have htrace : WordTrace (prefixWord ++ tailWord_4003293) baseStart_4003293 baseEnd_4003293 := by
    simpa [prefixWord, tailWord_4003293, baseEnd_4003293] using wordTrace_append hprefix tailTrace_4003293
  have hstable : (prefixWord ++ tailWord_4003293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003293).length < 2 ^ (prefixWord ++ tailWord_4003293).sum := by decide
  have hdescent : baseEnd_4003293 < baseStart_4003293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003338 : List Nat := [3, 1, 2, 2, 2, 3, 2, 7]
def baseStart_4003338 : Nat := 118140960795 + 4003338 * 2 ^ 59
def prefixEnd_4003338 : Nat := 4983230072969 + 3 ^ 40 * 4003338 * 2
def baseEnd_4003338 : Nat := 152269378993271344841777

theorem tailTrace_4003338 : CollatzResearch.WordTrace tailWord_4003338 prefixEnd_4003338 152269378993271344841777 := by
  unfold tailWord_4003338
  simp only [CollatzResearch.WordTrace]
  refine ⟨36503433092649404135530667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97342488247065077694748445 36503433092649404135530667)
  ·
    refine ⟨54755149638974106203296001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36503433092649404135530667 54755149638974106203296001)
    ·
      refine ⟨41066362229230579652472001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54755149638974106203296001 41066362229230579652472001)
      ·
        refine ⟨30799771671922934739354001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41066362229230579652472001 30799771671922934739354001)
        ·
          refine ⟨23099828753942201054515501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30799771671922934739354001 23099828753942201054515501)
          ·
            refine ⟨8662435782728325395443313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23099828753942201054515501 8662435782728325395443313)
            ·
              refine ⟨6496826837046244046582485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8662435782728325395443313 6496826837046244046582485)
              ·
                refine ⟨152269378993271344841777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6496826837046244046582485 152269378993271344841777)
                ·
                  rfl

theorem cell22_4003338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 7].length) (baseStart_4003338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003338 prefixEnd_4003338 := by exact prefixLift 4003338
  have htrace : WordTrace (prefixWord ++ tailWord_4003338) baseStart_4003338 baseEnd_4003338 := by
    simpa [prefixWord, tailWord_4003338, baseEnd_4003338] using wordTrace_append hprefix tailTrace_4003338
  have hstable : (prefixWord ++ tailWord_4003338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003338).length < 2 ^ (prefixWord ++ tailWord_4003338).sum := by decide
  have hdescent : baseEnd_4003338 < baseStart_4003338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003342 : List Nat := [4, 1, 1, 2, 4, 1, 1, 3, 2, 3]
def baseStart_4003342 : Nat := 118140960795 + 4003342 * 2 ^ 59
def prefixEnd_4003342 : Nat := 4983230072969 + 3 ^ 40 * 4003342 * 2
def baseEnd_4003342 : Nat := 1370425780221187426475981

theorem tailTrace_4003342 : CollatzResearch.WordTrace tailWord_4003342 prefixEnd_4003342 1370425780221187426475981 := by
  unfold tailWord_4003342
  simp only [CollatzResearch.WordTrace]
  refine ⟨18251734782822890653158535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97342585508388750150178853 18251734782822890653158535)
  ·
    refine ⟨27377602174234335979737803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18251734782822890653158535 27377602174234335979737803)
    ·
      refine ⟨41066403261351503969606705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27377602174234335979737803 41066403261351503969606705)
      ·
        refine ⟨30799802446013627977205029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41066403261351503969606705 30799802446013627977205029)
        ·
          refine ⟨5774962958627555245725943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30799802446013627977205029 5774962958627555245725943)
          ·
            refine ⟨8662444437941332868588915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5774962958627555245725943 8662444437941332868588915)
            ·
              refine ⟨12993666656911999302883373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8662444437941332868588915 12993666656911999302883373)
              ·
                refine ⟨4872624996341999738581265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12993666656911999302883373 4872624996341999738581265)
                ·
                  refine ⟨3654468747256499803935949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4872624996341999738581265 3654468747256499803935949)
                  ·
                    refine ⟨1370425780221187426475981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3654468747256499803935949 1370425780221187426475981)
                    ·
                      rfl

theorem cell22_4003342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_4003342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003342 prefixEnd_4003342 := by exact prefixLift 4003342
  have htrace : WordTrace (prefixWord ++ tailWord_4003342) baseStart_4003342 baseEnd_4003342 := by
    simpa [prefixWord, tailWord_4003342, baseEnd_4003342] using wordTrace_append hprefix tailTrace_4003342
  have hstable : (prefixWord ++ tailWord_4003342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003342).length < 2 ^ (prefixWord ++ tailWord_4003342).sum := by decide
  have hdescent : baseEnd_4003342 < baseStart_4003342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003383 : List Nat := [1, 1, 3, 1, 2, 4, 1, 4, 5]
def baseStart_4003383 : Nat := 118140960795 + 4003383 * 2 ^ 59
def prefixEnd_4003383 : Nat := 4983230072969 + 3 ^ 40 * 4003383 * 2
def baseEnd_4003383 : Nat := 456813271786358995400285

theorem tailTrace_4003383 : CollatzResearch.WordTrace tailWord_4003383 prefixEnd_4003383 456813271786358995400285 := by
  unfold tailWord_4003383
  simp only [CollatzResearch.WordTrace]
  refine ⟨146015373655434589227510803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97343582436956392818340535 146015373655434589227510803)
  ·
    refine ⟨219023060483151883841266205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146015373655434589227510803 219023060483151883841266205)
    ·
      refine ⟨82133647681181956440474827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219023060483151883841266205 82133647681181956440474827)
      ·
        refine ⟨123200471521772934660712241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82133647681181956440474827 123200471521772934660712241)
        ·
          refine ⟨92400353641329700995534181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123200471521772934660712241 92400353641329700995534181)
          ·
            refine ⟨17325066307749318936662659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92400353641329700995534181 17325066307749318936662659)
            ·
              refine ⟨25987599461623978404993989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17325066307749318936662659 25987599461623978404993989)
              ·
                refine ⟨4872674899054495950936373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25987599461623978404993989 4872674899054495950936373)
                ·
                  refine ⟨456813271786358995400285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4872674899054495950936373 456813271786358995400285)
                  ·
                    rfl

theorem cell22_4003383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 5].length) (baseStart_4003383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003383 prefixEnd_4003383 := by exact prefixLift 4003383
  have htrace : WordTrace (prefixWord ++ tailWord_4003383) baseStart_4003383 baseEnd_4003383 := by
    simpa [prefixWord, tailWord_4003383, baseEnd_4003383] using wordTrace_append hprefix tailTrace_4003383
  have hstable : (prefixWord ++ tailWord_4003383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003383).length < 2 ^ (prefixWord ++ tailWord_4003383).sum := by decide
  have hdescent : baseEnd_4003383 < baseStart_4003383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003445 : List Nat := [1, 3, 4, 2, 1, 1, 1, 3, 6]
def baseStart_4003445 : Nat := 118140960795 + 4003445 * 2 ^ 59
def prefixEnd_4003445 : Nat := 4983230072969 + 3 ^ 40 * 4003445 * 2
def baseEnd_4003445 : Nat := 456820346408709830383555

theorem tailTrace_4003445 : CollatzResearch.WordTrace tailWord_4003445 prefixEnd_4003445 456820346408709830383555 := by
  unfold tailWord_4003445
  simp only [CollatzResearch.WordTrace]
  refine ⟨146017634981209973816267789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97345089987473315877511859 146017634981209973816267789)
  ·
    refine ⟨54756613117953740181100421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146017634981209973816267789 54756613117953740181100421)
    ·
      refine ⟨10266864959616326283956329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54756613117953740181100421 10266864959616326283956329)
      ·
        refine ⟨7700148719712244712967247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10266864959616326283956329 7700148719712244712967247)
        ·
          refine ⟨11550223079568367069450871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7700148719712244712967247 11550223079568367069450871)
          ·
            refine ⟨17325334619352550604176307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11550223079568367069450871 17325334619352550604176307)
            ·
              refine ⟨25988001929028825906264461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17325334619352550604176307 25988001929028825906264461)
              ·
                refine ⟨9745500723385809714849173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25988001929028825906264461 9745500723385809714849173)
                ·
                  refine ⟨456820346408709830383555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9745500723385809714849173 456820346408709830383555)
                  ·
                    rfl

theorem cell22_4003445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_4003445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003445 prefixEnd_4003445 := by exact prefixLift 4003445
  have htrace : WordTrace (prefixWord ++ tailWord_4003445) baseStart_4003445 baseEnd_4003445 := by
    simpa [prefixWord, tailWord_4003445, baseEnd_4003445] using wordTrace_append hprefix tailTrace_4003445
  have hstable : (prefixWord ++ tailWord_4003445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003445).length < 2 ^ (prefixWord ++ tailWord_4003445).sum := by decide
  have hdescent : baseEnd_4003445 < baseStart_4003445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003464 : List Nat := [2, 1, 3, 5, 1, 1, 2, 2, 1, 4]
def baseStart_4003464 : Nat := 118140960795 + 4003464 * 2 ^ 59
def prefixEnd_4003464 : Nat := 4983230072969 + 3 ^ 40 * 4003464 * 2
def baseEnd_4003464 : Nat := 1370467543314419774925607

theorem tailTrace_4003464 : CollatzResearch.WordTrace tailWord_4003464 prefixEnd_4003464 1370467543314419774925607 := by
  unfold tailWord_4003464
  simp only [CollatzResearch.WordTrace]
  refine ⟨73009163984070570030604723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97345551978760760040806297 73009163984070570030604723)
  ·
    refine ⟨109513745976105855045907085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73009163984070570030604723 109513745976105855045907085)
    ·
      refine ⟨41067654741039695642215157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109513745976105855045907085 41067654741039695642215157)
      ·
        refine ⟨3850092631972471466457671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41067654741039695642215157 3850092631972471466457671)
        ·
          refine ⟨5775138947958707199686507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3850092631972471466457671 5775138947958707199686507)
          ·
            refine ⟨8662708421938060799529761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5775138947958707199686507 8662708421938060799529761)
            ·
              refine ⟨6497031316453545599647321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8662708421938060799529761 6497031316453545599647321)
              ·
                refine ⟨4872773487340159199735491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6497031316453545599647321 4872773487340159199735491)
                ·
                  refine ⟨7309160231010238799603237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4872773487340159199735491 7309160231010238799603237)
                  ·
                    refine ⟨1370467543314419774925607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7309160231010238799603237 1370467543314419774925607)
                    ·
                      rfl

theorem cell22_4003464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_4003464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003464 prefixEnd_4003464 := by exact prefixLift 4003464
  have htrace : WordTrace (prefixWord ++ tailWord_4003464) baseStart_4003464 baseEnd_4003464 := by
    simpa [prefixWord, tailWord_4003464, baseEnd_4003464] using wordTrace_append hprefix tailTrace_4003464
  have hstable : (prefixWord ++ tailWord_4003464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003464).length < 2 ^ (prefixWord ++ tailWord_4003464).sum := by decide
  have hdescent : baseEnd_4003464 < baseStart_4003464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003496 : List Nat := [2, 1, 7, 1, 1, 2, 1, 1, 6]
def baseStart_4003496 : Nat := 118140960795 + 4003496 * 2 ^ 59
def prefixEnd_4003496 : Nat := 4983230072969 + 3 ^ 40 * 4003496 * 2
def baseEnd_4003496 : Nat := 456826165856127452708503

theorem tailTrace_4003496 : CollatzResearch.WordTrace tailWord_4003496 prefixEnd_4003496 456826165856127452708503 := by
  unfold tailWord_4003496
  simp only [CollatzResearch.WordTrace]
  refine ⟨73009747552012604763187171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97346330069350139684249561 73009747552012604763187171)
  ·
    refine ⟨109514621328018907144780757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73009747552012604763187171 109514621328018907144780757)
    ·
      refine ⟨2566748937375443136205799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 109514621328018907144780757 2566748937375443136205799)
      ·
        refine ⟨3850123406063164704308699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2566748937375443136205799 3850123406063164704308699)
        ·
          refine ⟨5775185109094747056463049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3850123406063164704308699 5775185109094747056463049)
          ·
            refine ⟨4331388831821060292347287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5775185109094747056463049 4331388831821060292347287)
            ·
              refine ⟨6497083247731590438520931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4331388831821060292347287 6497083247731590438520931)
              ·
                refine ⟨9745624871597385657781397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6497083247731590438520931 9745624871597385657781397)
                ·
                  refine ⟨456826165856127452708503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9745624871597385657781397 456826165856127452708503)
                  ·
                    rfl

theorem cell22_4003496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 6].length) (baseStart_4003496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003496 prefixEnd_4003496 := by exact prefixLift 4003496
  have htrace : WordTrace (prefixWord ++ tailWord_4003496) baseStart_4003496 baseEnd_4003496 := by
    simpa [prefixWord, tailWord_4003496, baseEnd_4003496] using wordTrace_append hprefix tailTrace_4003496
  have hstable : (prefixWord ++ tailWord_4003496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003496).length < 2 ^ (prefixWord ++ tailWord_4003496).sum := by decide
  have hdescent : baseEnd_4003496 < baseStart_4003496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003503 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 2, 6]
def baseStart_4003503 : Nat := 118140960795 + 4003503 * 2 ^ 59
def prefixEnd_4003503 : Nat := 4983230072969 + 3 ^ 40 * 4003503 * 2
def baseEnd_4003503 : Nat := 1370480893811436673200487

theorem tailTrace_4003503 : CollatzResearch.WordTrace tailWord_4003503 prefixEnd_4003503 1370480893811436673200487 := by
  unfold tailWord_4003503
  simp only [CollatzResearch.WordTrace]
  refine ⟨146019750414999849721879163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97346500276666566481252775 146019750414999849721879163)
  ·
    refine ⟨219029625622499774582818745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146019750414999849721879163 219029625622499774582818745)
    ·
      refine ⟨164272219216874830937114059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219029625622499774582818745 164272219216874830937114059)
      ·
        refine ⟨246408328825312246405671089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164272219216874830937114059 246408328825312246405671089)
        ·
          refine ⟨184806246618984184804253317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246408328825312246405671089 184806246618984184804253317)
          ·
            refine ⟨34651171241059534650797497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184806246618984184804253317 34651171241059534650797497)
            ·
              refine ⟨25988378430794650988098123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34651171241059534650797497 25988378430794650988098123)
              ·
                refine ⟨38982567646191976482147185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25988378430794650988098123 38982567646191976482147185)
                ·
                  refine ⟨29236925734643982361610389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38982567646191976482147185 29236925734643982361610389)
                  ·
                    refine ⟨1370480893811436673200487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29236925734643982361610389 1370480893811436673200487)
                    ·
                      rfl

theorem cell22_4003503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_4003503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003503 prefixEnd_4003503 := by exact prefixLift 4003503
  have htrace : WordTrace (prefixWord ++ tailWord_4003503) baseStart_4003503 baseEnd_4003503 := by
    simpa [prefixWord, tailWord_4003503, baseEnd_4003503] using wordTrace_append hprefix tailTrace_4003503
  have hstable : (prefixWord ++ tailWord_4003503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003503).length < 2 ^ (prefixWord ++ tailWord_4003503).sum := by decide
  have hdescent : baseEnd_4003503 < baseStart_4003503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003526 : List Nat := [6, 1, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_4003526 : Nat := 118140960795 + 4003526 * 2 ^ 59
def prefixEnd_4003526 : Nat := 4983230072969 + 3 ^ 40 * 4003526 * 2
def baseEnd_4003526 : Nat := 1370488767181472279875417

theorem tailTrace_4003526 : CollatzResearch.WordTrace tailWord_4003526 prefixEnd_4003526 1370488767181472279875417 := by
  unfold tailWord_4003526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4563143415434891395311451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97347059529277683099977621 4563143415434891395311451)
  ·
    refine ⟨6844715123152337092967177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4563143415434891395311451 6844715123152337092967177)
    ·
      refine ⟨5133536342364252819725383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6844715123152337092967177 5133536342364252819725383)
      ·
        refine ⟨7700304513546379229588075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5133536342364252819725383 7700304513546379229588075)
        ·
          refine ⟨11550456770319568844382113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7700304513546379229588075 11550456770319568844382113)
          ·
            refine ⟨8662842577739676633286585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11550456770319568844382113 8662842577739676633286585)
            ·
              refine ⟨6497131933304757474964939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8662842577739676633286585 6497131933304757474964939)
              ·
                refine ⟨9745697899957136212447409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6497131933304757474964939 9745697899957136212447409)
                ·
                  refine ⟨7309273424967852159335557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9745697899957136212447409 7309273424967852159335557)
                  ·
                    refine ⟨1370488767181472279875417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7309273424967852159335557 1370488767181472279875417)
                    ·
                      rfl

theorem cell22_4003526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_4003526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003526 prefixEnd_4003526 := by exact prefixLift 4003526
  have htrace : WordTrace (prefixWord ++ tailWord_4003526) baseStart_4003526 baseEnd_4003526 := by
    simpa [prefixWord, tailWord_4003526, baseEnd_4003526] using wordTrace_append hprefix tailTrace_4003526
  have hstable : (prefixWord ++ tailWord_4003526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003526).length < 2 ^ (prefixWord ++ tailWord_4003526).sum := by decide
  have hdescent : baseEnd_4003526 < baseStart_4003526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003580 : List Nat := [2, 2, 2, 1, 3, 1, 3, 2, 6]
def baseStart_4003580 : Nat := 118140960795 + 4003580 * 2 ^ 59
def prefixEnd_4003580 : Nat := 4983230072969 + 3 ^ 40 * 4003580 * 2
def baseEnd_4003580 : Nat := 456835750828344713008417

theorem tailTrace_4003580 : CollatzResearch.WordTrace tailWord_4003580 prefixEnd_4003580 456835750828344713008417 := by
  unfold tailWord_4003580
  simp only [CollatzResearch.WordTrace]
  refine ⟨73011279417860445936216097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97348372557147261248288129 73011279417860445936216097)
  ·
    refine ⟨54758459563395334452162073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73011279417860445936216097 54758459563395334452162073)
    ·
      refine ⟨41068844672546500839121555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54758459563395334452162073 41068844672546500839121555)
      ·
        refine ⟨61603267008819751258682333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41068844672546500839121555 61603267008819751258682333)
        ·
          refine ⟨23101225128307406722005875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61603267008819751258682333 23101225128307406722005875)
          ·
            refine ⟨34651837692461110083008813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23101225128307406722005875 34651837692461110083008813)
            ·
              refine ⟨12994439134672916281128305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34651837692461110083008813 12994439134672916281128305)
              ·
                refine ⟨9745829351004687210846229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12994439134672916281128305 9745829351004687210846229)
                ·
                  refine ⟨456835750828344713008417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9745829351004687210846229 456835750828344713008417)
                  ·
                    rfl

theorem cell22_4003580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_4003580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003580 prefixEnd_4003580 := by exact prefixLift 4003580
  have htrace : WordTrace (prefixWord ++ tailWord_4003580) baseStart_4003580 baseEnd_4003580 := by
    simpa [prefixWord, tailWord_4003580, baseEnd_4003580] using wordTrace_append hprefix tailTrace_4003580
  have hstable : (prefixWord ++ tailWord_4003580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003580).length < 2 ^ (prefixWord ++ tailWord_4003580).sum := by decide
  have hdescent : baseEnd_4003580 < baseStart_4003580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003595 : List Nat := [1, 1, 1, 1, 5, 1, 4, 2, 1, 5]
def baseStart_4003595 : Nat := 118140960795 + 4003595 * 2 ^ 59
def prefixEnd_4003595 : Nat := 4983230072969 + 3 ^ 40 * 4003595 * 2
def baseEnd_4003595 : Nat := 1370512387291579099900205

theorem tailTrace_4003595 : CollatzResearch.WordTrace tailWord_4003595 prefixEnd_4003595 1370512387291579099900205 := by
  unfold tailWord_4003595
  simp only [CollatzResearch.WordTrace]
  refine ⟨146023105930666549434228239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97348737287111032956152159 146023105930666549434228239)
  ·
    refine ⟨219034658895999824151342359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146023105930666549434228239 219034658895999824151342359)
    ·
      refine ⟨328551988343999736227013539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219034658895999824151342359 328551988343999736227013539)
      ·
        refine ⟨492827982515999604340520309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328551988343999736227013539 492827982515999604340520309)
        ·
          refine ⟨46202623360874962906923779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 492827982515999604340520309 46202623360874962906923779)
          ·
            refine ⟨69303935041312444360385669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46202623360874962906923779 69303935041312444360385669)
            ·
              refine ⟨12994487820246083317572313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69303935041312444360385669 12994487820246083317572313)
              ·
                refine ⟨9745865865184562488179235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12994487820246083317572313 9745865865184562488179235)
                ·
                  refine ⟨14618798797776843732268853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9745865865184562488179235 14618798797776843732268853)
                  ·
                    refine ⟨1370512387291579099900205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14618798797776843732268853 1370512387291579099900205)
                    ·
                      rfl

theorem cell22_4003595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 5].length) (baseStart_4003595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003595 prefixEnd_4003595 := by exact prefixLift 4003595
  have htrace : WordTrace (prefixWord ++ tailWord_4003595) baseStart_4003595 baseEnd_4003595 := by
    simpa [prefixWord, tailWord_4003595, baseEnd_4003595] using wordTrace_append hprefix tailTrace_4003595
  have hstable : (prefixWord ++ tailWord_4003595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003595).length < 2 ^ (prefixWord ++ tailWord_4003595).sum := by decide
  have hdescent : baseEnd_4003595 < baseStart_4003595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003612 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 4, 3]
def baseStart_4003612 : Nat := 118140960795 + 4003612 * 2 ^ 59
def prefixEnd_4003612 : Nat := 4983230072969 + 3 ^ 40 * 4003612 * 2
def baseEnd_4003612 : Nat := 1370518206738996722225153

theorem tailTrace_4003612 : CollatzResearch.WordTrace tailWord_4003612 prefixEnd_4003612 1370518206738996722225153 := by
  unfold tailWord_4003612
  simp only [CollatzResearch.WordTrace]
  refine ⟨73011862985802480668798545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97349150647736640891731393 73011862985802480668798545)
  ·
    refine ⟨54758897239351860501598909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73011862985802480668798545 54758897239351860501598909)
    ·
      refine ⟨20534586464756947688099591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54758897239351860501598909 20534586464756947688099591)
      ·
        refine ⟨30801879697135421532149387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20534586464756947688099591 30801879697135421532149387)
        ·
          refine ⟨46202819545703132298224081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30801879697135421532149387 46202819545703132298224081)
          ·
            refine ⟨34652114659277349223668061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46202819545703132298224081 34652114659277349223668061)
            ·
              refine ⟨12994542997229005958875523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34652114659277349223668061 12994542997229005958875523)
              ·
                refine ⟨19491814495843508938313285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12994542997229005958875523 19491814495843508938313285)
                ·
                  refine ⟨3654715217970657925933741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19491814495843508938313285 3654715217970657925933741)
                  ·
                    refine ⟨1370518206738996722225153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3654715217970657925933741 1370518206738996722225153)
                    ·
                      rfl

theorem cell22_4003612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_4003612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003612 prefixEnd_4003612 := by exact prefixLift 4003612
  have htrace : WordTrace (prefixWord ++ tailWord_4003612) baseStart_4003612 baseEnd_4003612 := by
    simpa [prefixWord, tailWord_4003612, baseEnd_4003612] using wordTrace_append hprefix tailTrace_4003612
  have hstable : (prefixWord ++ tailWord_4003612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003612).length < 2 ^ (prefixWord ++ tailWord_4003612).sum := by decide
  have hdescent : baseEnd_4003612 < baseStart_4003612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003642 : List Nat := [3, 1, 1, 1, 5, 1, 4, 6]
def baseStart_4003642 : Nat := 118140960795 + 4003642 * 2 ^ 59
def prefixEnd_4003642 : Nat := 4983230072969 + 3 ^ 40 * 4003642 * 2
def baseEnd_4003642 : Nat := 152280941816898515997229

theorem tailTrace_4003642 : CollatzResearch.WordTrace tailWord_4003642 prefixEnd_4003642 152280941816898515997229 := by
  unfold tailWord_4003642
  simp only [CollatzResearch.WordTrace]
  refine ⟨36506205040374069115297295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97349880107664184307459453 36506205040374069115297295)
  ·
    refine ⟨54759307560561103672945943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36506205040374069115297295 54759307560561103672945943)
    ·
      refine ⟨82138961340841655509418915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54759307560561103672945943 82138961340841655509418915)
      ·
        refine ⟨123208442011262483264128373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82138961340841655509418915 123208442011262483264128373)
        ·
          refine ⟨11550791438555857806012035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123208442011262483264128373 11550791438555857806012035)
          ·
            refine ⟨17326187157833786709018053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11550791438555857806012035 17326187157833786709018053)
            ·
              refine ⟨3248660092093835007940885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17326187157833786709018053 3248660092093835007940885)
              ·
                refine ⟨152280941816898515997229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3248660092093835007940885 152280941816898515997229)
                ·
                  rfl

theorem cell22_4003642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 6].length) (baseStart_4003642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003642 prefixEnd_4003642 := by exact prefixLift 4003642
  have htrace : WordTrace (prefixWord ++ tailWord_4003642) baseStart_4003642 baseEnd_4003642 := by
    simpa [prefixWord, tailWord_4003642, baseEnd_4003642] using wordTrace_append hprefix tailTrace_4003642
  have hstable : (prefixWord ++ tailWord_4003642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003642).length < 2 ^ (prefixWord ++ tailWord_4003642).sum := by decide
  have hdescent : baseEnd_4003642 < baseStart_4003642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003685 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 1, 7]
def baseStart_4003685 : Nat := 118140960795 + 4003685 * 2 ^ 59
def prefixEnd_4003685 : Nat := 4983230072969 + 3 ^ 40 * 4003685 * 2
def baseEnd_4003685 : Nat := 1370543196130848865149929

theorem tailTrace_4003685 : CollatzResearch.WordTrace tailWord_4003685 prefixEnd_4003685 1370543196130848865149929 := by
  unfold tailWord_4003685
  simp only [CollatzResearch.WordTrace]
  refine ⟨146026388500340494805004509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97350925666893663203336339 146026388500340494805004509)
  ·
    refine ⟨54759895687627685551876691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146026388500340494805004509 54759895687627685551876691)
    ·
      refine ⟨82139843531441528327815037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54759895687627685551876691 82139843531441528327815037)
      ·
        refine ⟨30802441324290573122930639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82139843531441528327815037 30802441324290573122930639)
        ·
          refine ⟨46203661986435859684395959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30802441324290573122930639 46203661986435859684395959)
          ·
            refine ⟨69305492979653789526593939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46203661986435859684395959 69305492979653789526593939)
            ·
              refine ⟨103958239469480684289890909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69305492979653789526593939 103958239469480684289890909)
              ·
                refine ⟨38984339801055256608709091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103958239469480684289890909 38984339801055256608709091)
                ·
                  refine ⟨58476509701582884913063637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38984339801055256608709091 58476509701582884913063637)
                  ·
                    refine ⟨1370543196130848865149929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58476509701582884913063637 1370543196130848865149929)
                    ·
                      rfl

theorem cell22_4003685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_4003685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003685 prefixEnd_4003685 := by exact prefixLift 4003685
  have htrace : WordTrace (prefixWord ++ tailWord_4003685) baseStart_4003685 baseEnd_4003685 := by
    simpa [prefixWord, tailWord_4003685, baseEnd_4003685] using wordTrace_append hprefix tailTrace_4003685
  have hstable : (prefixWord ++ tailWord_4003685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003685).length < 2 ^ (prefixWord ++ tailWord_4003685).sum := by decide
  have hdescent : baseEnd_4003685 < baseStart_4003685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003687 : List Nat := [1, 1, 5, 1, 2, 1, 3, 3, 5]
def baseStart_4003687 : Nat := 118140960795 + 4003687 * 2 ^ 59
def prefixEnd_4003687 : Nat := 4983230072969 + 3 ^ 40 * 4003687 * 2
def baseEnd_4003687 : Nat := 456847960257240508866641

theorem tailTrace_4003687 : CollatzResearch.WordTrace tailWord_4003687 prefixEnd_4003687 456847960257240508866641 := by
  unfold tailWord_4003687
  simp only [CollatzResearch.WordTrace]
  refine ⟨146026461446333249146577315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97350974297555499431051543 146026461446333249146577315)
  ·
    refine ⟨219039692169499873719865973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146026461446333249146577315 219039692169499873719865973)
    ·
      refine ⟨20534971140890613161237435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219039692169499873719865973 20534971140890613161237435)
      ·
        refine ⟨30802456711335919741856153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20534971140890613161237435 30802456711335919741856153)
        ·
          refine ⟨23101842533501939806392115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30802456711335919741856153 23101842533501939806392115)
          ·
            refine ⟨34652763800252909709588173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23101842533501939806392115 34652763800252909709588173)
            ·
              refine ⟨12994786425094841141095565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34652763800252909709588173 12994786425094841141095565)
              ·
                refine ⟨4873044909410565427910837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12994786425094841141095565 4873044909410565427910837)
                ·
                  refine ⟨456847960257240508866641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4873044909410565427910837 456847960257240508866641)
                  ·
                    rfl

theorem cell22_4003687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 5].length) (baseStart_4003687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003687 prefixEnd_4003687 := by exact prefixLift 4003687
  have htrace : WordTrace (prefixWord ++ tailWord_4003687) baseStart_4003687 baseEnd_4003687 := by
    simpa [prefixWord, tailWord_4003687, baseEnd_4003687] using wordTrace_append hprefix tailTrace_4003687
  have hstable : (prefixWord ++ tailWord_4003687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003687).length < 2 ^ (prefixWord ++ tailWord_4003687).sum := by decide
  have hdescent : baseEnd_4003687 < baseStart_4003687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003747 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 6, 3]
def baseStart_4003747 : Nat := 118140960795 + 4003747 * 2 ^ 59
def prefixEnd_4003747 : Nat := 4983230072969 + 3 ^ 40 * 4003747 * 2
def baseEnd_4003747 : Nat := 1370564419997901370099739

theorem tailTrace_4003747 : CollatzResearch.WordTrace tailWord_4003747 prefixEnd_4003747 1370564419997901370099739 := by
  unfold tailWord_4003747
  simp only [CollatzResearch.WordTrace]
  refine ⟨146028649826115879393761495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97352433217410586262507663 146028649826115879393761495)
  ·
    refine ⟨219042974739173819090642243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146028649826115879393761495 219042974739173819090642243)
    ·
      refine ⟨328564462108760728635963365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219042974739173819090642243 328564462108760728635963365)
      ·
        refine ⟨61605836645392636619243131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328564462108760728635963365 61605836645392636619243131)
        ·
          refine ⟨92408754968088954928864697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61605836645392636619243131 92408754968088954928864697)
          ·
            refine ⟨69306566226066716196648523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92408754968088954928864697 69306566226066716196648523)
            ·
              refine ⟨103959849339100074294972785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69306566226066716196648523 103959849339100074294972785)
              ·
                refine ⟨77969887004325055721229589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103959849339100074294972785 77969887004325055721229589)
                ·
                  refine ⟨3654838453327736986932637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77969887004325055721229589 3654838453327736986932637)
                  ·
                    refine ⟨1370564419997901370099739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3654838453327736986932637 1370564419997901370099739)
                    ·
                      rfl

theorem cell22_4003747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 3].length) (baseStart_4003747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003747 prefixEnd_4003747 := by exact prefixLift 4003747
  have htrace : WordTrace (prefixWord ++ tailWord_4003747) baseStart_4003747 baseEnd_4003747 := by
    simpa [prefixWord, tailWord_4003747, baseEnd_4003747] using wordTrace_append hprefix tailTrace_4003747
  have hstable : (prefixWord ++ tailWord_4003747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003747).length < 2 ^ (prefixWord ++ tailWord_4003747).sum := by decide
  have hdescent : baseEnd_4003747 < baseStart_4003747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003798 : List Nat := [5, 2, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_4003798 : Nat := 118140960795 + 4003798 * 2 ^ 59
def prefixEnd_4003798 : Nat := 4983230072969 + 3 ^ 40 * 4003798 * 2
def baseEnd_4003798 : Nat := 1370581878340154237074583

theorem tailTrace_4003798 : CollatzResearch.WordTrace tailWord_4003798 prefixEnd_4003798 1370581878340154237074583 := by
  unfold tailWord_4003798
  simp only [CollatzResearch.WordTrace]
  refine ⟨9126906871808194693991753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97353673299287410069245365 9126906871808194693991753)
  ·
    refine ⟨6845180153856146020493815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9126906871808194693991753 6845180153856146020493815)
    ·
      refine ⟨10267770230784219030740723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6845180153856146020493815 10267770230784219030740723)
      ·
        refine ⟨15401655346176328546111085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10267770230784219030740723 15401655346176328546111085)
        ·
          refine ⟨5775620754816123204791657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15401655346176328546111085 5775620754816123204791657)
          ·
            refine ⟨4331715566112092403593743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5775620754816123204791657 4331715566112092403593743)
            ·
              refine ⟨6497573349168138605390615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4331715566112092403593743 6497573349168138605390615)
              ·
                refine ⟨9746360023752207908085923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6497573349168138605390615 9746360023752207908085923)
                ·
                  refine ⟨14619540035628311862128885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9746360023752207908085923 14619540035628311862128885)
                  ·
                    refine ⟨1370581878340154237074583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14619540035628311862128885 1370581878340154237074583)
                    ·
                      rfl

theorem cell22_4003798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_4003798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003798 prefixEnd_4003798 := by exact prefixLift 4003798
  have htrace : WordTrace (prefixWord ++ tailWord_4003798) baseStart_4003798 baseEnd_4003798 := by
    simpa [prefixWord, tailWord_4003798, baseEnd_4003798] using wordTrace_append hprefix tailTrace_4003798
  have hstable : (prefixWord ++ tailWord_4003798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003798).length < 2 ^ (prefixWord ++ tailWord_4003798).sum := by decide
  have hdescent : baseEnd_4003798 < baseStart_4003798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003809 : List Nat := [1, 2, 3, 1, 2, 1, 4, 2, 3, 3]
def baseStart_4003809 : Nat := 118140960795 + 4003809 * 2 ^ 59
def prefixEnd_4003809 : Nat := 4983230072969 + 3 ^ 40 * 4003809 * 2
def baseEnd_4003809 : Nat := 1370585643864953875049549

theorem tailTrace_4003809 : CollatzResearch.WordTrace tailWord_4003809 prefixEnd_4003809 1370585643864953875049549 := by
  unfold tailWord_4003809
  simp only [CollatzResearch.WordTrace]
  refine ⟨146030911151891263982518481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97353940767927509321678987 146030911151891263982518481)
  ·
    refine ⟨109523183363918447986888861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146030911151891263982518481 109523183363918447986888861)
    ·
      refine ⟨41071193761469417995083323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109523183363918447986888861 41071193761469417995083323)
      ·
        refine ⟨61606790642204126992624985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41071193761469417995083323 61606790642204126992624985)
        ·
          refine ⟨46205092981653095244468739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61606790642204126992624985 46205092981653095244468739)
          ·
            refine ⟨69307639472479642866703109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46205092981653095244468739 69307639472479642866703109)
            ·
              refine ⟨12995182401089933037506833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69307639472479642866703109 12995182401089933037506833)
              ·
                refine ⟨9746386800817449778130125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12995182401089933037506833 9746386800817449778130125)
                ·
                  refine ⟨3654895050306543666798797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9746386800817449778130125 3654895050306543666798797)
                  ·
                    refine ⟨1370585643864953875049549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3654895050306543666798797 1370585643864953875049549)
                    ·
                      rfl

theorem cell22_4003809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_4003809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003809 prefixEnd_4003809 := by exact prefixLift 4003809
  have htrace : WordTrace (prefixWord ++ tailWord_4003809) baseStart_4003809 baseEnd_4003809 := by
    simpa [prefixWord, tailWord_4003809, baseEnd_4003809] using wordTrace_append hprefix tailTrace_4003809
  have hstable : (prefixWord ++ tailWord_4003809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003809).length < 2 ^ (prefixWord ++ tailWord_4003809).sum := by decide
  have hdescent : baseEnd_4003809 < baseStart_4003809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003837 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_4003837 : Nat := 118140960795 + 4003837 * 2 ^ 59
def prefixEnd_4003837 : Nat := 4983230072969 + 3 ^ 40 * 4003837 * 2
def baseEnd_4003837 : Nat := 1370595228837171135349463

theorem tailTrace_4003837 : CollatzResearch.WordTrace tailWord_4003837 prefixEnd_4003837 1370595228837171135349463 := by
  unfold tailWord_4003837
  simp only [CollatzResearch.WordTrace]
  refine ⟨146031932395789824764537765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97354621597193216509691843 146031932395789824764537765)
  ·
    refine ⟨27380987324210592143350831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146031932395789824764537765 27380987324210592143350831)
    ·
      refine ⟨41071480986315888215026247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27380987324210592143350831 41071480986315888215026247)
      ·
        refine ⟨61607221479473832322539371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41071480986315888215026247 61607221479473832322539371)
        ·
          refine ⟨92410832219210748483809057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61607221479473832322539371 92410832219210748483809057)
          ·
            refine ⟨69308124164408061362856793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92410832219210748483809057 69308124164408061362856793)
            ·
              refine ⟨51981093123306046022142595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69308124164408061362856793 51981093123306046022142595)
              ·
                refine ⟨77971639684959069033213893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51981093123306046022142595 77971639684959069033213893)
                ·
                  refine ⟨14619682440929825443727605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77971639684959069033213893 14619682440929825443727605)
                  ·
                    refine ⟨1370595228837171135349463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14619682440929825443727605 1370595228837171135349463)
                    ·
                      rfl

theorem cell22_4003837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_4003837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003837 prefixEnd_4003837 := by exact prefixLift 4003837
  have htrace : WordTrace (prefixWord ++ tailWord_4003837) baseStart_4003837 baseEnd_4003837 := by
    simpa [prefixWord, tailWord_4003837, baseEnd_4003837] using wordTrace_append hprefix tailTrace_4003837
  have hstable : (prefixWord ++ tailWord_4003837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003837).length < 2 ^ (prefixWord ++ tailWord_4003837).sum := by decide
  have hdescent : baseEnd_4003837 < baseStart_4003837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003901 : List Nat := [1, 4, 1, 3, 1, 1, 3, 4, 4]
def baseStart_4003901 : Nat := 118140960795 + 4003901 * 2 ^ 59
def prefixEnd_4003901 : Nat := 4983230072969 + 3 ^ 40 * 4003901 * 2
def baseEnd_4003901 : Nat := 456872379115032100583089

theorem tailTrace_4003901 : CollatzResearch.WordTrace tailWord_4003901 prefixEnd_4003901 456872379115032100583089 := by
  unfold tailWord_4003901
  simp only [CollatzResearch.WordTrace]
  refine ⟨146034266667557963694867557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97356177778371975796578371 146034266667557963694867557)
  ·
    refine ⟨27381425000167118192787667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146034266667557963694867557 27381425000167118192787667)
    ·
      refine ⟨41072137500250677289181501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27381425000167118192787667 41072137500250677289181501)
      ·
        refine ⟨15402051562594003983443063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41072137500250677289181501 15402051562594003983443063)
        ·
          refine ⟨23103077343891005975164595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15402051562594003983443063 23103077343891005975164595)
          ·
            refine ⟨34654616015836508962746893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23103077343891005975164595 34654616015836508962746893)
            ·
              refine ⟨12995481005938690861030085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34654616015836508962746893 12995481005938690861030085)
              ·
                refine ⟨2436652688613504536443141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12995481005938690861030085 2436652688613504536443141)
                ·
                  refine ⟨456872379115032100583089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2436652688613504536443141 456872379115032100583089)
                  ·
                    rfl

theorem cell22_4003901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_4003901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003901 prefixEnd_4003901 := by exact prefixLift 4003901
  have htrace : WordTrace (prefixWord ++ tailWord_4003901) baseStart_4003901 baseEnd_4003901 := by
    simpa [prefixWord, tailWord_4003901, baseEnd_4003901] using wordTrace_append hprefix tailTrace_4003901
  have hstable : (prefixWord ++ tailWord_4003901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003901).length < 2 ^ (prefixWord ++ tailWord_4003901).sum := by decide
  have hdescent : baseEnd_4003901 < baseStart_4003901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003912 : List Nat := [2, 1, 3, 1, 1, 1, 2, 11]
def baseStart_4003912 : Nat := 118140960795 + 4003912 * 2 ^ 59
def prefixEnd_4003912 : Nat := 4983230072969 + 3 ^ 40 * 4003912 * 2
def baseEnd_4003912 : Nat := 152291211429988437747137

theorem tailTrace_4003912 : CollatzResearch.WordTrace tailWord_4003912 prefixEnd_4003912 152291211429988437747137 := by
  unfold tailWord_4003912
  simp only [CollatzResearch.WordTrace]
  refine ⟨73017333935259056286758995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97356445247012075049011993 73017333935259056286758995)
  ·
    refine ⟨109526000902888584430138493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73017333935259056286758995 109526000902888584430138493)
    ·
      refine ⟨41072250338583219161301935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109526000902888584430138493 41072250338583219161301935)
      ·
        refine ⟨61608375507874828741952903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41072250338583219161301935 61608375507874828741952903)
        ·
          refine ⟨92412563261812243112929355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61608375507874828741952903 92412563261812243112929355)
          ·
            refine ⟨138618844892718364669394033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92412563261812243112929355 138618844892718364669394033)
            ·
              refine ⟨103964133669538773502045525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138618844892718364669394033 103964133669538773502045525)
              ·
                refine ⟨152291211429988437747137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 103964133669538773502045525 152291211429988437747137)
                ·
                  rfl

theorem cell22_4003912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 11].length) (baseStart_4003912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003912 prefixEnd_4003912 := by exact prefixLift 4003912
  have htrace : WordTrace (prefixWord ++ tailWord_4003912) baseStart_4003912 baseEnd_4003912 := by
    simpa [prefixWord, tailWord_4003912, baseEnd_4003912] using wordTrace_append hprefix tailTrace_4003912
  have hstable : (prefixWord ++ tailWord_4003912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003912).length < 2 ^ (prefixWord ++ tailWord_4003912).sum := by decide
  have hdescent : baseEnd_4003912 < baseStart_4003912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003916 : List Nat := [2, 2, 1, 3, 1, 1, 4, 3, 2, 3]
def baseStart_4003916 : Nat := 118140960795 + 4003916 * 2 ^ 59
def prefixEnd_4003916 : Nat := 4983230072969 + 3 ^ 40 * 4003916 * 2
def baseEnd_4003916 : Nat := 1370622272151641262624221

theorem tailTrace_4003916 : CollatzResearch.WordTrace tailWord_4003916 prefixEnd_4003916 1370622272151641262624221 := by
  unfold tailWord_4003916
  simp only [CollatzResearch.WordTrace]
  refine ⟨73017406881251810628331801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97356542508335747504442401 73017406881251810628331801)
  ·
    refine ⟨54763055160938857971248851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73017406881251810628331801 54763055160938857971248851)
    ·
      refine ⟨82144582741408286956873277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54763055160938857971248851 82144582741408286956873277)
      ·
        refine ⟨30804218528028107608827479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82144582741408286956873277 30804218528028107608827479)
        ·
          refine ⟨46206327792042161413241219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30804218528028107608827479 46206327792042161413241219)
          ·
            refine ⟨69309491688063242119861829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46206327792042161413241219 69309491688063242119861829)
            ·
              refine ⟨12995529691511857897474093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69309491688063242119861829 12995529691511857897474093)
              ·
                refine ⟨4873323634316946711552785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12995529691511857897474093 4873323634316946711552785)
                ·
                  refine ⟨3654992725737710033664589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4873323634316946711552785 3654992725737710033664589)
                  ·
                    refine ⟨1370622272151641262624221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3654992725737710033664589 1370622272151641262624221)
                    ·
                      rfl

theorem cell22_4003916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_4003916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003916 prefixEnd_4003916 := by exact prefixLift 4003916
  have htrace : WordTrace (prefixWord ++ tailWord_4003916) baseStart_4003916 baseEnd_4003916 := by
    simpa [prefixWord, tailWord_4003916, baseEnd_4003916] using wordTrace_append hprefix tailTrace_4003916
  have hstable : (prefixWord ++ tailWord_4003916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003916).length < 2 ^ (prefixWord ++ tailWord_4003916).sum := by decide
  have hdescent : baseEnd_4003916 < baseStart_4003916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003929 : List Nat := [1, 2, 1, 2, 2, 1, 7, 6]
def baseStart_4003929 : Nat := 118140960795 + 4003929 * 2 ^ 59
def prefixEnd_4003929 : Nat := 4983230072969 + 3 ^ 40 * 4003929 * 2
def baseEnd_4003929 : Nat := 152291858035257062449909

theorem tailTrace_4003929 : CollatzResearch.WordTrace tailWord_4003929 prefixEnd_4003929 152291858035257062449909 := by
  unfold tailWord_4003929
  simp only [CollatzResearch.WordTrace]
  refine ⟨146035287911456524476886841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97356858607637682984591227 146035287911456524476886841)
  ·
    refine ⟨109526465933592393357665131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146035287911456524476886841 109526465933592393357665131)
    ·
      refine ⟨164289698900388590036497697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109526465933592393357665131 164289698900388590036497697)
      ·
        refine ⟨123217274175291442527373273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164289698900388590036497697 123217274175291442527373273)
        ·
          refine ⟨92412955631468581895529955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123217274175291442527373273 92412955631468581895529955)
          ·
            refine ⟨138619433447202872843294933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92412955631468581895529955 138619433447202872843294933)
            ·
              refine ⟨3248892971418817332264725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 138619433447202872843294933 3248892971418817332264725)
              ·
                refine ⟨152291858035257062449909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3248892971418817332264725 152291858035257062449909)
                ·
                  rfl

theorem cell22_4003929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 6].length) (baseStart_4003929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003929 prefixEnd_4003929 := by exact prefixLift 4003929
  have htrace : WordTrace (prefixWord ++ tailWord_4003929) baseStart_4003929 baseEnd_4003929 := by
    simpa [prefixWord, tailWord_4003929, baseEnd_4003929] using wordTrace_append hprefix tailTrace_4003929
  have hstable : (prefixWord ++ tailWord_4003929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003929).length < 2 ^ (prefixWord ++ tailWord_4003929).sum := by decide
  have hdescent : baseEnd_4003929 < baseStart_4003929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003961 : List Nat := [1, 2, 1, 3, 4, 1, 1, 3, 3, 3]
def baseStart_4003961 : Nat := 118140960795 + 4003961 * 2 ^ 59
def prefixEnd_4003961 : Nat := 4983230072969 + 3 ^ 40 * 4003961 * 2
def baseEnd_4003961 : Nat := 1370637676571276145249083

theorem tailTrace_4003961 : CollatzResearch.WordTrace tailWord_4003961 prefixEnd_4003961 1370637676571276145249083 := by
  unfold tailWord_4003961
  simp only [CollatzResearch.WordTrace]
  refine ⟨146036455047340593942051737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97357636698227062628034491 146036455047340593942051737)
  ·
    refine ⟨109527341285505445456538803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146036455047340593942051737 109527341285505445456538803)
    ·
      refine ⟨164291011928258168184808205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109527341285505445456538803 164291011928258168184808205)
      ·
        refine ⟨61609129473096813069303077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164291011928258168184808205 61609129473096813069303077)
        ·
          refine ⟨11551711776205652450494327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61609129473096813069303077 11551711776205652450494327)
          ·
            refine ⟨17327567664308478675741491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11551711776205652450494327 17327567664308478675741491)
            ·
              refine ⟨25991351496462718013612237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17327567664308478675741491 25991351496462718013612237)
              ·
                refine ⟨9746756811173519255104589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25991351496462718013612237 9746756811173519255104589)
                ·
                  refine ⟨3655033804190069720664221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9746756811173519255104589 3655033804190069720664221)
                  ·
                    refine ⟨1370637676571276145249083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3655033804190069720664221 1370637676571276145249083)
                    ·
                      rfl

theorem cell22_4003961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 3].length) (baseStart_4003961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4003961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4003961 prefixEnd_4003961 := by exact prefixLift 4003961
  have htrace : WordTrace (prefixWord ++ tailWord_4003961) baseStart_4003961 baseEnd_4003961 := by
    simpa [prefixWord, tailWord_4003961, baseEnd_4003961] using wordTrace_append hprefix tailTrace_4003961
  have hstable : (prefixWord ++ tailWord_4003961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003961).length < 2 ^ (prefixWord ++ tailWord_4003961).sum := by decide
  have hdescent : baseEnd_4003961 < baseStart_4003961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004049 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 1, 6]
def baseStart_4004049 : Nat := 118140960795 + 4004049 * 2 ^ 59
def prefixEnd_4004049 : Nat := 4983230072969 + 3 ^ 40 * 4004049 * 2
def baseEnd_4004049 : Nat := 1370667800769673249048813

theorem tailTrace_4004049 : CollatzResearch.WordTrace tailWord_4004049 prefixEnd_4004049 1370667800769673249048813 := by
  unfold tailWord_4004049
  simp only [CollatzResearch.WordTrace]
  refine ⟨146039664671021784971255201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97359776447347856647503467 146039664671021784971255201)
  ·
    refine ⟨109529748503266338728441401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146039664671021784971255201 109529748503266338728441401)
    ·
      refine ⟨82147311377449754046331051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109529748503266338728441401 82147311377449754046331051)
      ·
        refine ⟨123220967066174631069496577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82147311377449754046331051 123220967066174631069496577)
        ·
          refine ⟨92415725299630973302122433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123220967066174631069496577 92415725299630973302122433)
          ·
            refine ⟨69311793974723229976591825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92415725299630973302122433 69311793974723229976591825)
            ·
              refine ⟨51983845481042422482443869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69311793974723229976591825 51983845481042422482443869)
              ·
                refine ⟨19493942055390908430916451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51983845481042422482443869 19493942055390908430916451)
                ·
                  refine ⟨29240913083086362646374677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19493942055390908430916451 29240913083086362646374677)
                  ·
                    refine ⟨1370667800769673249048813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29240913083086362646374677 1370667800769673249048813)
                    ·
                      rfl

theorem cell22_4004049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_4004049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004049 prefixEnd_4004049 := by exact prefixLift 4004049
  have htrace : WordTrace (prefixWord ++ tailWord_4004049) baseStart_4004049 baseEnd_4004049 := by
    simpa [prefixWord, tailWord_4004049, baseEnd_4004049] using wordTrace_append hprefix tailTrace_4004049
  have hstable : (prefixWord ++ tailWord_4004049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004049).length < 2 ^ (prefixWord ++ tailWord_4004049).sum := by decide
  have hdescent : baseEnd_4004049 < baseStart_4004049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004096 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 5, 3]
def baseStart_4004096 : Nat := 118140960795 + 4004096 * 2 ^ 59
def prefixEnd_4004096 : Nat := 4983230072969 + 3 ^ 40 * 4004096 * 2
def baseEnd_4004096 : Nat := 1370683889830180793123669

theorem tailTrace_4004096 : CollatzResearch.WordTrace tailWord_4004096 prefixEnd_4004096 1370683889830180793123669 := by
  unfold tailWord_4004096
  simp only [CollatzResearch.WordTrace]
  refine ⟨73020689450925755999108071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97360919267901007998810761 73020689450925755999108071)
  ·
    refine ⟨109531034176388633998662107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73020689450925755999108071 109531034176388633998662107)
    ·
      refine ⟨164296551264582950997993161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109531034176388633998662107 164296551264582950997993161)
      ·
        refine ⟨123222413448437213248494871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164296551264582950997993161 123222413448437213248494871)
        ·
          refine ⟨184833620172655819872742307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123222413448437213248494871 184833620172655819872742307)
          ·
            refine ⟨277250430258983729809113461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184833620172655819872742307 277250430258983729809113461)
            ·
              refine ⟨25992227836779724669604387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277250430258983729809113461 25992227836779724669604387)
              ·
                refine ⟨38988341755169587004406581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25992227836779724669604387 38988341755169587004406581)
                ·
                  refine ⟨3655157039547148781663117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38988341755169587004406581 3655157039547148781663117)
                  ·
                    refine ⟨1370683889830180793123669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3655157039547148781663117 1370683889830180793123669)
                    ·
                      rfl

theorem cell22_4004096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 5, 3].length) (baseStart_4004096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004096 prefixEnd_4004096 := by exact prefixLift 4004096
  have htrace : WordTrace (prefixWord ++ tailWord_4004096) baseStart_4004096 baseEnd_4004096 := by
    simpa [prefixWord, tailWord_4004096, baseEnd_4004096] using wordTrace_append hprefix tailTrace_4004096
  have hstable : (prefixWord ++ tailWord_4004096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004096).length < 2 ^ (prefixWord ++ tailWord_4004096).sum := by decide
  have hdescent : baseEnd_4004096 < baseStart_4004096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004100 : List Nat := [2, 3, 2, 2, 3, 2, 1, 1, 2, 4]
def baseStart_4004100 : Nat := 118140960795 + 4004100 * 2 ^ 59
def prefixEnd_4004100 : Nat := 4983230072969 + 3 ^ 40 * 4004100 * 2
def baseEnd_4004100 : Nat := 1370685259111926116023657

theorem tailTrace_4004100 : CollatzResearch.WordTrace tailWord_4004100 prefixEnd_4004100 1370685259111926116023657 := by
  unfold tailWord_4004100
  simp only [CollatzResearch.WordTrace]
  refine ⟨73020762396918510340680877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97361016529224680454241169 73020762396918510340680877)
  ·
    refine ⟨27382785898844441377755329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73020762396918510340680877 27382785898844441377755329)
    ·
      refine ⟨20537089424133331033316497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27382785898844441377755329 20537089424133331033316497)
      ·
        refine ⟨15402817068099998274987373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20537089424133331033316497 15402817068099998274987373)
        ·
          refine ⟨5776056400537499353120265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15402817068099998274987373 5776056400537499353120265)
          ·
            refine ⟨4332042300403124514840199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5776056400537499353120265 4332042300403124514840199)
            ·
              refine ⟨6498063450604686772260299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4332042300403124514840199 6498063450604686772260299)
              ·
                refine ⟨9747095175907030158390449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6498063450604686772260299 9747095175907030158390449)
                ·
                  refine ⟨7310321381930272618792837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9747095175907030158390449 7310321381930272618792837)
                  ·
                    refine ⟨1370685259111926116023657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7310321381930272618792837 1370685259111926116023657)
                    ·
                      rfl

theorem cell22_4004100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_4004100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004100 prefixEnd_4004100 := by exact prefixLift 4004100
  have htrace : WordTrace (prefixWord ++ tailWord_4004100) baseStart_4004100 baseEnd_4004100 := by
    simpa [prefixWord, tailWord_4004100, baseEnd_4004100] using wordTrace_append hprefix tailTrace_4004100
  have hstable : (prefixWord ++ tailWord_4004100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004100).length < 2 ^ (prefixWord ++ tailWord_4004100).sum := by decide
  have hdescent : baseEnd_4004100 < baseStart_4004100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004130 : List Nat := [3, 3, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_4004130 : Nat := 118140960795 + 4004130 * 2 ^ 59
def prefixEnd_4004130 : Nat := 4983230072969 + 3 ^ 40 * 4004130 * 2
def baseEnd_4004130 : Nat := 1370695528725016037773565

theorem tailTrace_4004130 : CollatzResearch.WordTrace tailWord_4004130 prefixEnd_4004130 1370695528725016037773565 := by
  unfold tailWord_4004130
  simp only [CollatzResearch.WordTrace]
  refine ⟨36510654745932083951238461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97361745989152223869969229 36510654745932083951238461)
  ·
    refine ⟨13691495529724531481714423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36510654745932083951238461 13691495529724531481714423)
    ·
      refine ⟨20537243294586797222571635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13691495529724531481714423 20537243294586797222571635)
      ·
        refine ⟨30805864941880195833857453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20537243294586797222571635 30805864941880195833857453)
        ·
          refine ⟨11552199353205073437696545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30805864941880195833857453 11552199353205073437696545)
          ·
            refine ⟨8664149514903805078272409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11552199353205073437696545 8664149514903805078272409)
            ·
              refine ⟨6498112136177853808704307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8664149514903805078272409 6498112136177853808704307)
              ·
                refine ⟨9747168204266780713056461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6498112136177853808704307 9747168204266780713056461)
                ·
                  refine ⟨3655188076600042767396173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9747168204266780713056461 3655188076600042767396173)
                  ·
                    refine ⟨1370695528725016037773565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3655188076600042767396173 1370695528725016037773565)
                    ·
                      rfl

theorem cell22_4004130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_4004130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004130 prefixEnd_4004130 := by exact prefixLift 4004130
  have htrace : WordTrace (prefixWord ++ tailWord_4004130) baseStart_4004130 baseEnd_4004130 := by
    simpa [prefixWord, tailWord_4004130, baseEnd_4004130] using wordTrace_append hprefix tailTrace_4004130
  have hstable : (prefixWord ++ tailWord_4004130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004130).length < 2 ^ (prefixWord ++ tailWord_4004130).sum := by decide
  have hdescent : baseEnd_4004130 < baseStart_4004130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004201 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 4, 4]
def baseStart_4004201 : Nat := 118140960795 + 4004201 * 2 ^ 59
def prefixEnd_4004201 : Nat := 4983230072969 + 3 ^ 40 * 4004201 * 2
def baseEnd_4004201 : Nat := 1370719833475995519248347

theorem tailTrace_4004201 : CollatzResearch.WordTrace tailWord_4004201 prefixEnd_4004201 1370719833475995519248347 := by
  unfold tailWord_4004201
  simp only [CollatzResearch.WordTrace]
  refine ⟨146045208566471114930788457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97363472377647409953858971 146045208566471114930788457)
  ·
    refine ⟨109533906424853336198091343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146045208566471114930788457 109533906424853336198091343)
    ·
      refine ⟨164300859637280004297137015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109533906424853336198091343 164300859637280004297137015)
      ·
        refine ⟨246451289455920006445705523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164300859637280004297137015 246451289455920006445705523)
        ·
          refine ⟨369676934183880009668558285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246451289455920006445705523 369676934183880009668558285)
          ·
            refine ⟨138628850318955003625709357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369676934183880009668558285 138628850318955003625709357)
            ·
              refine ⟨51985818869608126359641009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138628850318955003625709357 51985818869608126359641009)
              ·
                refine ⟨38989364152206094769730757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51985818869608126359641009 38989364152206094769730757)
                ·
                  refine ⟨7310505778538642769324517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38989364152206094769730757 7310505778538642769324517)
                  ·
                    refine ⟨1370719833475995519248347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7310505778538642769324517 1370719833475995519248347)
                    ·
                      rfl

theorem cell22_4004201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_4004201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004201 prefixEnd_4004201 := by exact prefixLift 4004201
  have htrace : WordTrace (prefixWord ++ tailWord_4004201) baseStart_4004201 baseEnd_4004201 := by
    simpa [prefixWord, tailWord_4004201, baseEnd_4004201] using wordTrace_append hprefix tailTrace_4004201
  have hstable : (prefixWord ++ tailWord_4004201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004201).length < 2 ^ (prefixWord ++ tailWord_4004201).sum := by decide
  have hdescent : baseEnd_4004201 < baseStart_4004201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004203 : List Nat := [1, 1, 1, 1, 2, 2, 2, 7, 2, 3]
def baseStart_4004203 : Nat := 118140960795 + 4004203 * 2 ^ 59
def prefixEnd_4004203 : Nat := 4983230072969 + 3 ^ 40 * 4004203 * 2
def baseEnd_4004203 : Nat := 1370720518116868180698341

theorem tailTrace_4004203 : CollatzResearch.WordTrace tailWord_4004203 prefixEnd_4004203 1370720518116868180698341 := by
  unfold tailWord_4004203
  simp only [CollatzResearch.WordTrace]
  refine ⟨146045281512463869272361263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97363521008309246181574175 146045281512463869272361263)
  ·
    refine ⟨219067922268695803908541895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146045281512463869272361263 219067922268695803908541895)
    ·
      refine ⟨328601883403043705862812843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219067922268695803908541895 328601883403043705862812843)
      ·
        refine ⟨492902825104565558794219265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328601883403043705862812843 492902825104565558794219265)
        ·
          refine ⟨369677118828424169095664449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492902825104565558794219265 369677118828424169095664449)
          ·
            refine ⟨277257839121318126821748337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369677118828424169095664449 277257839121318126821748337)
            ·
              refine ⟨207943379340988595116311253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277257839121318126821748337 207943379340988595116311253)
              ·
                refine ⟨4873672953304420198038545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 207943379340988595116311253 4873672953304420198038545)
                ·
                  refine ⟨3655254714978315148528909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4873672953304420198038545 3655254714978315148528909)
                  ·
                    refine ⟨1370720518116868180698341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3655254714978315148528909 1370720518116868180698341)
                    ·
                      rfl

theorem cell22_4004203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 3].length) (baseStart_4004203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004203 prefixEnd_4004203 := by exact prefixLift 4004203
  have htrace : WordTrace (prefixWord ++ tailWord_4004203) baseStart_4004203 baseEnd_4004203 := by
    simpa [prefixWord, tailWord_4004203, baseEnd_4004203] using wordTrace_append hprefix tailTrace_4004203
  have hstable : (prefixWord ++ tailWord_4004203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004203).length < 2 ^ (prefixWord ++ tailWord_4004203).sum := by decide
  have hdescent : baseEnd_4004203 < baseStart_4004203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004269 : List Nat := [1, 5, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_4004269 : Nat := 118140960795 + 4004269 * 2 ^ 59
def prefixEnd_4004269 : Nat := 4983230072969 + 3 ^ 40 * 4004269 * 2
def baseEnd_4004269 : Nat := 1370743111265666008548139

theorem tailTrace_4004269 : CollatzResearch.WordTrace tailWord_4004269 prefixEnd_4004269 1370743111265666008548139 := by
  unfold tailWord_4004269
  simp only [CollatzResearch.WordTrace]
  refine ⟨146047688730224762544263861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97365125820149841696175907 146047688730224762544263861)
  ·
    refine ⟨13691970818458571488524737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146047688730224762544263861 13691970818458571488524737)
    ·
      refine ⟨10268978113843928616393553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13691970818458571488524737 10268978113843928616393553)
      ·
        refine ⟨7701733585382946462295165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10268978113843928616393553 7701733585382946462295165)
        ·
          refine ⟨2888150094518604923360687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7701733585382946462295165 2888150094518604923360687)
          ·
            refine ⟨4332225141777907385041031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2888150094518604923360687 4332225141777907385041031)
            ·
              refine ⟨6498337712666861077561547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4332225141777907385041031 6498337712666861077561547)
              ·
                refine ⟨9747506569000291616342321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6498337712666861077561547 9747506569000291616342321)
                ·
                  refine ⟨7310629926750218712256741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9747506569000291616342321 7310629926750218712256741)
                  ·
                    refine ⟨1370743111265666008548139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7310629926750218712256741 1370743111265666008548139)
                    ·
                      rfl

theorem cell22_4004269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_4004269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004269 prefixEnd_4004269 := by exact prefixLift 4004269
  have htrace : WordTrace (prefixWord ++ tailWord_4004269) baseStart_4004269 baseEnd_4004269 := by
    simpa [prefixWord, tailWord_4004269, baseEnd_4004269] using wordTrace_append hprefix tailTrace_4004269
  have hstable : (prefixWord ++ tailWord_4004269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004269).length < 2 ^ (prefixWord ++ tailWord_4004269).sum := by decide
  have hdescent : baseEnd_4004269 < baseStart_4004269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004295 : List Nat := [1, 1, 4, 1, 1, 6, 1, 2, 5]
def baseStart_4004295 : Nat := 118140960795 + 4004295 * 2 ^ 59
def prefixEnd_4004295 : Nat := 4983230072969 + 3 ^ 40 * 4004295 * 2
def baseEnd_4004295 : Nat := 456917337199003535799353

theorem tailTrace_4004295 : CollatzResearch.WordTrace tailWord_4004295 prefixEnd_4004295 456917337199003535799353 := by
  unfold tailWord_4004295
  simp only [CollatzResearch.WordTrace]
  refine ⟨146048637028130568984710339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97365758018753712656473559 146048637028130568984710339)
  ·
    refine ⟨219072955542195853477065509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146048637028130568984710339 219072955542195853477065509)
    ·
      refine ⟨41076179164161722526949783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219072955542195853477065509 41076179164161722526949783)
      ·
        refine ⟨61614268746242583790424675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41076179164161722526949783 61614268746242583790424675)
        ·
          refine ⟨92421403119363875685637013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61614268746242583790424675 92421403119363875685637013)
          ·
            refine ⟨4332253271220181672764235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92421403119363875685637013 4332253271220181672764235)
            ·
              refine ⟨6498379906830272509146353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4332253271220181672764235 6498379906830272509146353)
              ·
                refine ⟨4873784930122704381859765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6498379906830272509146353 4873784930122704381859765)
                ·
                  refine ⟨456917337199003535799353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4873784930122704381859765 456917337199003535799353)
                  ·
                    rfl

theorem cell22_4004295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 5].length) (baseStart_4004295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004295 prefixEnd_4004295 := by exact prefixLift 4004295
  have htrace : WordTrace (prefixWord ++ tailWord_4004295) baseStart_4004295 baseEnd_4004295 := by
    simpa [prefixWord, tailWord_4004295, baseEnd_4004295] using wordTrace_append hprefix tailTrace_4004295
  have hstable : (prefixWord ++ tailWord_4004295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004295).length < 2 ^ (prefixWord ++ tailWord_4004295).sum := by decide
  have hdescent : baseEnd_4004295 < baseStart_4004295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004310 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_4004310 : Nat := 118140960795 + 4004310 * 2 ^ 59
def prefixEnd_4004310 : Nat := 4983230072969 + 3 ^ 40 * 4004310 * 2
def baseEnd_4004310 : Nat := 1370757146403555568273013

theorem tailTrace_4004310 : CollatzResearch.WordTrace tailWord_4004310 prefixEnd_4004310 1370757146403555568273013 := by
  unfold tailWord_4004310
  simp only [CollatzResearch.WordTrace]
  refine ⟨9128074007692264159156649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97366122748717484364337589 9128074007692264159156649)
  ·
    refine ⟨6846055505769198119367487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9128074007692264159156649 6846055505769198119367487)
    ·
      refine ⟨10269083258653797179051231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6846055505769198119367487 10269083258653797179051231)
      ·
        refine ⟨15403624887980695768576847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10269083258653797179051231 15403624887980695768576847)
        ·
          refine ⟨23105437331971043652865271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15403624887980695768576847 23105437331971043652865271)
          ·
            refine ⟨34658155997956565479297907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23105437331971043652865271 34658155997956565479297907)
            ·
              refine ⟨51987233996934848218946861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34658155997956565479297907 51987233996934848218946861)
              ·
                refine ⟨19495212748850568082105073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51987233996934848218946861 19495212748850568082105073)
                ·
                  refine ⟨14621409561637926061578805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19495212748850568082105073 14621409561637926061578805)
                  ·
                    refine ⟨1370757146403555568273013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14621409561637926061578805 1370757146403555568273013)
                    ·
                      rfl

theorem cell22_4004310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_4004310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004310 prefixEnd_4004310 := by exact prefixLift 4004310
  have htrace : WordTrace (prefixWord ++ tailWord_4004310) baseStart_4004310 baseEnd_4004310 := by
    simpa [prefixWord, tailWord_4004310, baseEnd_4004310] using wordTrace_append hprefix tailTrace_4004310
  have hstable : (prefixWord ++ tailWord_4004310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004310).length < 2 ^ (prefixWord ++ tailWord_4004310).sum := by decide
  have hdescent : baseEnd_4004310 < baseStart_4004310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004355 : List Nat := [1, 1, 1, 3, 2, 1, 4, 4, 2, 3]
def baseStart_4004355 : Nat := 118140960795 + 4004355 * 2 ^ 59
def prefixEnd_4004355 : Nat := 4983230072969 + 3 ^ 40 * 4004355 * 2
def baseEnd_4004355 : Nat := 1370772550823190450897875

theorem tailTrace_4004355 : CollatzResearch.WordTrace tailWord_4004355 prefixEnd_4004355 1370772550823190450897875 := by
  unfold tailWord_4004355
  simp only [CollatzResearch.WordTrace]
  refine ⟨146050825407913199231894519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97367216938608799487929679 146050825407913199231894519)
  ·
    refine ⟨219076238111869798847841779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146050825407913199231894519 219076238111869798847841779)
    ·
      refine ⟨328614357167804698271762669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219076238111869798847841779 328614357167804698271762669)
      ·
        refine ⟨123230383937926761851911001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328614357167804698271762669 123230383937926761851911001)
        ·
          refine ⟨92422787953445071388933251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123230383937926761851911001 92422787953445071388933251)
          ·
            refine ⟨138634181930167607083399877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92422787953445071388933251 138634181930167607083399877)
            ·
              refine ⟨25993909111906426328137477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138634181930167607083399877 25993909111906426328137477)
              ·
                refine ⟨4873857958482454936525777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25993909111906426328137477 4873857958482454936525777)
                ·
                  refine ⟨3655393468861841202394333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4873857958482454936525777 3655393468861841202394333)
                  ·
                    refine ⟨1370772550823190450897875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3655393468861841202394333 1370772550823190450897875)
                    ·
                      rfl

theorem cell22_4004355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 3].length) (baseStart_4004355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004355 prefixEnd_4004355 := by exact prefixLift 4004355
  have htrace : WordTrace (prefixWord ++ tailWord_4004355) baseStart_4004355 baseEnd_4004355 := by
    simpa [prefixWord, tailWord_4004355, baseEnd_4004355] using wordTrace_append hprefix tailTrace_4004355
  have hstable : (prefixWord ++ tailWord_4004355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004355).length < 2 ^ (prefixWord ++ tailWord_4004355).sum := by decide
  have hdescent : baseEnd_4004355 < baseStart_4004355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004430 : List Nat := [4, 1, 1, 1, 1, 2, 4, 3, 5]
def baseStart_4004430 : Nat := 118140960795 + 4004430 * 2 ^ 59
def prefixEnd_4004430 : Nat := 4983230072969 + 3 ^ 40 * 4004430 * 2
def baseEnd_4004430 : Nat := 456932741618638418424215

theorem tailTrace_4004430 : CollatzResearch.WordTrace tailWord_4004430 prefixEnd_4004430 456932741618638418424215 := by
  unfold tailWord_4004430
  simp only [CollatzResearch.WordTrace]
  refine ⟨18256695110330185880109343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97369040588427658027249829 18256695110330185880109343)
  ·
    refine ⟨27385042665495278820164015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18256695110330185880109343 27385042665495278820164015)
    ·
      refine ⟨41077563998242918230246023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27385042665495278820164015 41077563998242918230246023)
      ·
        refine ⟨61616345997364377345369035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41077563998242918230246023 61616345997364377345369035)
        ·
          refine ⟨92424518996046566018053553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61616345997364377345369035 92424518996046566018053553)
          ·
            refine ⟨69318389247034924513540165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92424518996046566018053553 69318389247034924513540165)
            ·
              refine ⟨12997197983819048346288781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69318389247034924513540165 12997197983819048346288781)
              ·
                refine ⟨4873949243932143129858293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12997197983819048346288781 4873949243932143129858293)
                ·
                  refine ⟨456932741618638418424215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4873949243932143129858293 456932741618638418424215)
                  ·
                    rfl

theorem cell22_4004430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_4004430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004430 prefixEnd_4004430 := by exact prefixLift 4004430
  have htrace : WordTrace (prefixWord ++ tailWord_4004430) baseStart_4004430 baseEnd_4004430 := by
    simpa [prefixWord, tailWord_4004430, baseEnd_4004430] using wordTrace_append hprefix tailTrace_4004430
  have hstable : (prefixWord ++ tailWord_4004430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004430).length < 2 ^ (prefixWord ++ tailWord_4004430).sum := by decide
  have hdescent : baseEnd_4004430 < baseStart_4004430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004464 : List Nat := [2, 1, 1, 1, 8, 1, 1, 2, 5]
def baseStart_4004464 : Nat := 118140960795 + 4004464 * 2 ^ 59
def prefixEnd_4004464 : Nat := 4983230072969 + 3 ^ 40 * 4004464 * 2
def baseEnd_4004464 : Nat := 456936621250250166640847

theorem tailTrace_4004464 : CollatzResearch.WordTrace tailWord_4004464 prefixEnd_4004464 456936621250250166640847 := by
  unfold tailWord_4004464
  simp only [CollatzResearch.WordTrace]
  refine ⟨73027400482259155423806223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97369867309678873898408297 73027400482259155423806223)
  ·
    refine ⟨109541100723388733135709335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73027400482259155423806223 109541100723388733135709335)
    ·
      refine ⟨164311651085083099703564003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109541100723388733135709335 164311651085083099703564003)
      ·
        refine ⟨246467476627624649555346005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164311651085083099703564003 246467476627624649555346005)
        ·
          refine ⟨2888290741729976361976711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 246467476627624649555346005 2888290741729976361976711)
          ·
            refine ⟨4332436112594964542965067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2888290741729976361976711 4332436112594964542965067)
            ·
              refine ⟨6498654168892446814447601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4332436112594964542965067 6498654168892446814447601)
              ·
                refine ⟨4873990626669335110835701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6498654168892446814447601 4873990626669335110835701)
                ·
                  refine ⟨456936621250250166640847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4873990626669335110835701 456936621250250166640847)
                  ·
                    rfl

theorem cell22_4004464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 5].length) (baseStart_4004464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004464 prefixEnd_4004464 := by exact prefixLift 4004464
  have htrace : WordTrace (prefixWord ++ tailWord_4004464) baseStart_4004464 baseEnd_4004464 := by
    simpa [prefixWord, tailWord_4004464, baseEnd_4004464] using wordTrace_append hprefix tailTrace_4004464
  have hstable : (prefixWord ++ tailWord_4004464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004464).length < 2 ^ (prefixWord ++ tailWord_4004464).sum := by decide
  have hdescent : baseEnd_4004464 < baseStart_4004464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004505 : List Nat := [1, 2, 1, 2, 1, 2, 4, 3, 2, 4]
def baseStart_4004505 : Nat := 118140960795 + 4004505 * 2 ^ 59
def prefixEnd_4004505 : Nat := 4983230072969 + 3 ^ 40 * 4004505 * 2
def baseEnd_4004505 : Nat := 1370823898888640059647415

theorem tailTrace_4004505 : CollatzResearch.WordTrace tailWord_4004505 prefixEnd_4004505 1370823898888640059647415 := by
  unfold tailWord_4004505
  simp only [CollatzResearch.WordTrace]
  refine ⟨146056296357369774849854969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97370864238246516566569979 146056296357369774849854969)
  ·
    refine ⟨109542222268027331137391227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146056296357369774849854969 109542222268027331137391227)
    ·
      refine ⟨164313333402040996706086841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109542222268027331137391227 164313333402040996706086841)
      ·
        refine ⟨123235000051530747529565131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164313333402040996706086841 123235000051530747529565131)
        ·
          refine ⟨184852500077296121294347697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123235000051530747529565131 184852500077296121294347697)
          ·
            refine ⟨138639375057972090970760773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184852500077296121294347697 138639375057972090970760773)
            ·
              refine ⟨25994882823369767057017645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138639375057972090970760773 25994882823369767057017645)
              ·
                refine ⟨9748081058763662646381617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25994882823369767057017645 9748081058763662646381617)
                ·
                  refine ⟨7311060794072746984786213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9748081058763662646381617 7311060794072746984786213)
                  ·
                    refine ⟨1370823898888640059647415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7311060794072746984786213 1370823898888640059647415)
                    ·
                      rfl

theorem cell22_4004505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_4004505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004505 prefixEnd_4004505 := by exact prefixLift 4004505
  have htrace : WordTrace (prefixWord ++ tailWord_4004505) baseStart_4004505 baseEnd_4004505 := by
    simpa [prefixWord, tailWord_4004505, baseEnd_4004505] using wordTrace_append hprefix tailTrace_4004505
  have hstable : (prefixWord ++ tailWord_4004505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004505).length < 2 ^ (prefixWord ++ tailWord_4004505).sum := by decide
  have hdescent : baseEnd_4004505 < baseStart_4004505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004541 : List Nat := [1, 4, 1, 2, 1, 5, 2, 1, 2, 3]
def baseStart_4004541 : Nat := 118140960795 + 4004541 * 2 ^ 59
def prefixEnd_4004541 : Nat := 4983230072969 + 3 ^ 40 * 4004541 * 2
def baseEnd_4004541 : Nat := 1370836222424347965747305

theorem tailTrace_4004541 : CollatzResearch.WordTrace tailWord_4004541 prefixEnd_4004541 1370836222424347965747305 := by
  unfold tailWord_4004541
  simp only [CollatzResearch.WordTrace]
  refine ⟨146057609385239352998165477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97371739590159568665443651 146057609385239352998165477)
  ·
    refine ⟨27385801759732378687156027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146057609385239352998165477 27385801759732378687156027)
    ·
      refine ⟨41078702639598568030734041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27385801759732378687156027 41078702639598568030734041)
      ·
        refine ⟨30809026979698926023050531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41078702639598568030734041 30809026979698926023050531)
        ·
          refine ⟨46213540469548389034575797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30809026979698926023050531 46213540469548389034575797)
          ·
            refine ⟨4332519419020161471991481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46213540469548389034575797 4332519419020161471991481)
            ·
              refine ⟨3249389564265121103993611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4332519419020161471991481 3249389564265121103993611)
              ·
                refine ⟨4874084346397681655990417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3249389564265121103993611 4874084346397681655990417)
                ·
                  refine ⟨3655563259798261241992813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4874084346397681655990417 3655563259798261241992813)
                  ·
                    refine ⟨1370836222424347965747305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3655563259798261241992813 1370836222424347965747305)
                    ·
                      rfl

theorem cell22_4004541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_4004541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004541 prefixEnd_4004541 := by exact prefixLift 4004541
  have htrace : WordTrace (prefixWord ++ tailWord_4004541) baseStart_4004541 baseEnd_4004541 := by
    simpa [prefixWord, tailWord_4004541, baseEnd_4004541] using wordTrace_append hprefix tailTrace_4004541
  have hstable : (prefixWord ++ tailWord_4004541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004541).length < 2 ^ (prefixWord ++ tailWord_4004541).sum := by decide
  have hdescent : baseEnd_4004541 < baseStart_4004541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004569 : List Nat := [1, 2, 1, 2, 3, 2, 2, 5, 1, 3]
def baseStart_4004569 : Nat := 118140960795 + 4004569 * 2 ^ 59
def prefixEnd_4004569 : Nat := 4983230072969 + 3 ^ 40 * 4004569 * 2
def baseEnd_4004569 : Nat := 1370845807396565226047219

theorem tailTrace_4004569 : CollatzResearch.WordTrace tailWord_4004569 prefixEnd_4004569 1370845807396565226047219 := by
  unfold tailWord_4004569
  simp only [CollatzResearch.WordTrace]
  refine ⟨146058630629137913780184761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97372420419425275853456507 146058630629137913780184761)
  ·
    refine ⟨109543972971853435335138571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146058630629137913780184761 109543972971853435335138571)
    ·
      refine ⟨164315959457780153002707857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109543972971853435335138571 164315959457780153002707857)
      ·
        refine ⟨123236969593335114752030893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164315959457780153002707857 123236969593335114752030893)
        ·
          refine ⟨46213863597500668032011585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123236969593335114752030893 46213863597500668032011585)
          ·
            refine ⟨34660397698125501024008689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46213863597500668032011585 34660397698125501024008689)
            ·
              refine ⟨25995298273594125768006517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34660397698125501024008689 25995298273594125768006517)
              ·
                refine ⟨2437059213149449290750611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25995298273594125768006517 2437059213149449290750611)
                ·
                  refine ⟨3655588819724173936125917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2437059213149449290750611 3655588819724173936125917)
                  ·
                    refine ⟨1370845807396565226047219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3655588819724173936125917 1370845807396565226047219)
                    ·
                      rfl

theorem cell22_4004569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 1, 3].length) (baseStart_4004569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004569 prefixEnd_4004569 := by exact prefixLift 4004569
  have htrace : WordTrace (prefixWord ++ tailWord_4004569) baseStart_4004569 baseEnd_4004569 := by
    simpa [prefixWord, tailWord_4004569, baseEnd_4004569] using wordTrace_append hprefix tailTrace_4004569
  have hstable : (prefixWord ++ tailWord_4004569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004569).length < 2 ^ (prefixWord ++ tailWord_4004569).sum := by decide
  have hdescent : baseEnd_4004569 < baseStart_4004569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004612 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_4004612 : Nat := 118140960795 + 4004612 * 2 ^ 59
def prefixEnd_4004612 : Nat := 4983230072969 + 3 ^ 40 * 4004612 * 2
def baseEnd_4004612 : Nat := 1370860527175327447222087

theorem tailTrace_4004612 : CollatzResearch.WordTrace tailWord_4004612 prefixEnd_4004612 1370860527175327447222087 := by
  unfold tailWord_4004612
  simp only [CollatzResearch.WordTrace]
  refine ⟨73030099483991066062000045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97373465978654754749333393 73030099483991066062000045)
  ·
    refine ⟨27386287306496649773250017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73030099483991066062000045 27386287306496649773250017)
    ·
      refine ⟨20539715479872487329937513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27386287306496649773250017 20539715479872487329937513)
      ·
        refine ⟨15404786609904365497453135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20539715479872487329937513 15404786609904365497453135)
        ·
          refine ⟨23107179914856548246179703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15404786609904365497453135 23107179914856548246179703)
          ·
            refine ⟨34660769872284822369269555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23107179914856548246179703 34660769872284822369269555)
            ·
              refine ⟨51991154808427233553904333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34660769872284822369269555 51991154808427233553904333)
              ·
                refine ⟨19496683053160212582714125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51991154808427233553904333 19496683053160212582714125)
                ·
                  refine ⟨7311256144935079718517797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19496683053160212582714125 7311256144935079718517797)
                  ·
                    refine ⟨1370860527175327447222087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7311256144935079718517797 1370860527175327447222087)
                    ·
                      rfl

theorem cell22_4004612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_4004612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004612 prefixEnd_4004612 := by exact prefixLift 4004612
  have htrace : WordTrace (prefixWord ++ tailWord_4004612) baseStart_4004612 baseEnd_4004612 := by
    simpa [prefixWord, tailWord_4004612, baseEnd_4004612] using wordTrace_append hprefix tailTrace_4004612
  have hstable : (prefixWord ++ tailWord_4004612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004612).length < 2 ^ (prefixWord ++ tailWord_4004612).sum := by decide
  have hdescent : baseEnd_4004612 < baseStart_4004612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004644 : List Nat := [2, 3, 1, 3, 3, 1, 2, 1, 6]
def baseStart_4004644 : Nat := 118140960795 + 4004644 * 2 ^ 59
def prefixEnd_4004644 : Nat := 4983230072969 + 3 ^ 40 * 4004644 * 2
def baseEnd_4004644 : Nat := 456957160476430010140663

theorem tailTrace_4004644 : CollatzResearch.WordTrace tailWord_4004644 prefixEnd_4004644 456957160476430010140663 := by
  unfold tailWord_4004644
  simp only [CollatzResearch.WordTrace]
  refine ⟨73030683051933100794582493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97374244069244134392776657 73030683051933100794582493)
  ·
    refine ⟨27386506144474912797968435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73030683051933100794582493 27386506144474912797968435)
    ·
      refine ⟨41079759216712369196952653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27386506144474912797968435 41079759216712369196952653)
      ·
        refine ⟨15404909706267138448857245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41079759216712369196952653 15404909706267138448857245)
        ·
          refine ⟨5776841139850176918321467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15404909706267138448857245 5776841139850176918321467)
          ·
            refine ⟨8665261709775265377482201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5776841139850176918321467 8665261709775265377482201)
            ·
              refine ⟨6498946282331449033111651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8665261709775265377482201 6498946282331449033111651)
              ·
                refine ⟨9748419423497173549667477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6498946282331449033111651 9748419423497173549667477)
                ·
                  refine ⟨456957160476430010140663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9748419423497173549667477 456957160476430010140663)
                  ·
                    rfl

theorem cell22_4004644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_4004644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004644 prefixEnd_4004644 := by exact prefixLift 4004644
  have htrace : WordTrace (prefixWord ++ tailWord_4004644) baseStart_4004644 baseEnd_4004644 := by
    simpa [prefixWord, tailWord_4004644, baseEnd_4004644] using wordTrace_append hprefix tailTrace_4004644
  have hstable : (prefixWord ++ tailWord_4004644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004644).length < 2 ^ (prefixWord ++ tailWord_4004644).sum := by decide
  have hdescent : baseEnd_4004644 < baseStart_4004644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004659 : List Nat := [1, 1, 1, 2, 6, 3, 1, 1, 1, 5]
def baseStart_4004659 : Nat := 118140960795 + 4004659 * 2 ^ 59
def prefixEnd_4004659 : Nat := 4983230072969 + 3 ^ 40 * 4004659 * 2
def baseEnd_4004659 : Nat := 1370876616235834991296943

theorem tailTrace_4004659 : CollatzResearch.WordTrace tailWord_4004659 prefixEnd_4004659 1370876616235834991296943 := by
  unfold tailWord_4004659
  simp only [CollatzResearch.WordTrace]
  refine ⟨146061913198811859150961031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97374608799207906100640687 146061913198811859150961031)
  ·
    refine ⟨219092869798217788726441547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146061913198811859150961031 219092869798217788726441547)
    ·
      refine ⟨328639304697326683089662321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219092869798217788726441547 328639304697326683089662321)
      ·
        refine ⟨246479478522995012317246741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328639304697326683089662321 246479478522995012317246741)
        ·
          refine ⟨11553725555765391202370941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 246479478522995012317246741 11553725555765391202370941)
          ·
            refine ⟨4332647083412021700889103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11553725555765391202370941 4332647083412021700889103)
            ·
              refine ⟨6498970625118032551333655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4332647083412021700889103 6498970625118032551333655)
              ·
                refine ⟨9748455937677048827000483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6498970625118032551333655 9748455937677048827000483)
                ·
                  refine ⟨14622683906515573240500725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9748455937677048827000483 14622683906515573240500725)
                  ·
                    refine ⟨1370876616235834991296943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14622683906515573240500725 1370876616235834991296943)
                    ·
                      rfl

theorem cell22_4004659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 5].length) (baseStart_4004659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004659 prefixEnd_4004659 := by exact prefixLift 4004659
  have htrace : WordTrace (prefixWord ++ tailWord_4004659) baseStart_4004659 baseEnd_4004659 := by
    simpa [prefixWord, tailWord_4004659, baseEnd_4004659] using wordTrace_append hprefix tailTrace_4004659
  have hstable : (prefixWord ++ tailWord_4004659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004659).length < 2 ^ (prefixWord ++ tailWord_4004659).sum := by decide
  have hdescent : baseEnd_4004659 < baseStart_4004659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004689 : List Nat := [1, 2, 2, 1, 7, 1, 8]
def baseStart_4004689 : Nat := 118140960795 + 4004689 * 2 ^ 59
def prefixEnd_4004689 : Nat := 4983230072969 + 3 ^ 40 * 4004689 * 2
def baseEnd_4004689 : Nat := 50773588364774996779513

theorem tailTrace_4004689 : CollatzResearch.WordTrace tailWord_4004689 prefixEnd_4004689 50773588364774996779513 := by
  unfold tailWord_4004689
  simp only [CollatzResearch.WordTrace]
  refine ⟨146063007388703174274553121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97375338259135449516368747 146063007388703174274553121)
  ·
    refine ⟨109547255541527380705914841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146063007388703174274553121 109547255541527380705914841)
    ·
      refine ⟨82160441656145535529436131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109547255541527380705914841 82160441656145535529436131)
      ·
        refine ⟨123240662484218303294154197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82160441656145535529436131 123240662484218303294154197)
        ·
          refine ⟨2888453026973866483456739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 123240662484218303294154197 2888453026973866483456739)
          ·
            refine ⟨4332679540460799725185109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2888453026973866483456739 4332679540460799725185109)
            ·
              refine ⟨50773588364774996779513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4332679540460799725185109 50773588364774996779513)
              ·
                rfl

theorem cell22_4004689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 8].length) (baseStart_4004689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004689 prefixEnd_4004689 := by exact prefixLift 4004689
  have htrace : WordTrace (prefixWord ++ tailWord_4004689) baseStart_4004689 baseEnd_4004689 := by
    simpa [prefixWord, tailWord_4004689, baseEnd_4004689] using wordTrace_append hprefix tailTrace_4004689
  have hstable : (prefixWord ++ tailWord_4004689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004689).length < 2 ^ (prefixWord ++ tailWord_4004689).sum := by decide
  have hdescent : baseEnd_4004689 < baseStart_4004689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004794 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 4, 3]
def baseStart_4004794 : Nat := 118140960795 + 4004794 * 2 ^ 59
def prefixEnd_4004794 : Nat := 4983230072969 + 3 ^ 40 * 4004794 * 2
def baseEnd_4004794 : Nat := 1370922829494739639171529

theorem tailTrace_4004794 : CollatzResearch.WordTrace tailWord_4004794 prefixEnd_4004794 1370922829494739639171529 := by
  unfold tailWord_4004794
  simp only [CollatzResearch.WordTrace]
  refine ⟨36516709263330694301781359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97377891368881851471416957 36516709263330694301781359)
  ·
    refine ⟨54775063894996041452672039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36516709263330694301781359 54775063894996041452672039)
    ·
      refine ⟨82162595842494062179008059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54775063894996041452672039 82162595842494062179008059)
      ·
        refine ⟨123243893763741093268512089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82162595842494062179008059 123243893763741093268512089)
        ·
          refine ⟨92432920322805819951384067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123243893763741093268512089 92432920322805819951384067)
          ·
            refine ⟨138649380484208729927076101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92432920322805819951384067 138649380484208729927076101)
            ·
              refine ⟨25996758840789136861326769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138649380484208729927076101 25996758840789136861326769)
              ·
                refine ⟨19497569130591852645995077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25996758840789136861326769 19497569130591852645995077)
                ·
                  refine ⟨3655794211985972371124077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19497569130591852645995077 3655794211985972371124077)
                  ·
                    refine ⟨1370922829494739639171529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3655794211985972371124077 1370922829494739639171529)
                    ·
                      rfl

theorem cell22_4004794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_4004794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004794 prefixEnd_4004794 := by exact prefixLift 4004794
  have htrace : WordTrace (prefixWord ++ tailWord_4004794) baseStart_4004794 baseEnd_4004794 := by
    simpa [prefixWord, tailWord_4004794, baseEnd_4004794] using wordTrace_append hprefix tailTrace_4004794
  have hstable : (prefixWord ++ tailWord_4004794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004794).length < 2 ^ (prefixWord ++ tailWord_4004794).sum := by decide
  have hdescent : baseEnd_4004794 < baseStart_4004794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004811 : List Nat := [1, 1, 1, 1, 3, 5, 3, 2, 2, 3]
def baseStart_4004811 : Nat := 118140960795 + 4004811 * 2 ^ 59
def prefixEnd_4004811 : Nat := 4983230072969 + 3 ^ 40 * 4004811 * 2
def baseEnd_4004811 : Nat := 1370928648942157261496477

theorem tailTrace_4004811 : CollatzResearch.WordTrace tailWord_4004811 prefixEnd_4004811 1370928648942157261496477 := by
  unfold tailWord_4004811
  simp only [CollatzResearch.WordTrace]
  refine ⟨146067457094261189110494287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97378304729507459406996191 146067457094261189110494287)
  ·
    refine ⟨219101185641391783665741431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146067457094261189110494287 219101185641391783665741431)
    ·
      refine ⟨328651778462087675498612147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219101185641391783665741431 328651778462087675498612147)
      ·
        refine ⟨492977667693131513247918221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328651778462087675498612147 492977667693131513247918221)
        ·
          refine ⟨184866625384924317467969333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 492977667693131513247918221 184866625384924317467969333)
          ·
            refine ⟨17331246129836654762622125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184866625384924317467969333 17331246129836654762622125)
            ·
              refine ⟨6499217298688745535983297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17331246129836654762622125 6499217298688745535983297)
              ·
                refine ⟨4874412974016559151987473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6499217298688745535983297 4874412974016559151987473)
                ·
                  refine ⟨3655809730512419363990605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4874412974016559151987473 3655809730512419363990605)
                  ·
                    refine ⟨1370928648942157261496477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3655809730512419363990605 1370928648942157261496477)
                    ·
                      rfl

theorem cell22_4004811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 3].length) (baseStart_4004811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004811 prefixEnd_4004811 := by exact prefixLift 4004811
  have htrace : WordTrace (prefixWord ++ tailWord_4004811) baseStart_4004811 baseEnd_4004811 := by
    simpa [prefixWord, tailWord_4004811, baseEnd_4004811] using wordTrace_append hprefix tailTrace_4004811
  have hstable : (prefixWord ++ tailWord_4004811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004811).length < 2 ^ (prefixWord ++ tailWord_4004811).sum := by decide
  have hdescent : baseEnd_4004811 < baseStart_4004811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004869 : List Nat := [1, 3, 1, 1, 2, 3, 2, 4, 5]
def baseStart_4004869 : Nat := 118140960795 + 4004869 * 2 ^ 59
def prefixEnd_4004869 : Nat := 4983230072969 + 3 ^ 40 * 4004869 * 2
def baseEnd_4004869 : Nat := 456982834509154814515433

theorem tailTrace_4004869 : CollatzResearch.WordTrace tailWord_4004869 prefixEnd_4004869 456982834509154814515433 := by
  unfold tailWord_4004869
  simp only [CollatzResearch.WordTrace]
  refine ⟨146069572528051065016105661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97379715018700710010737107 146069572528051065016105661)
  ·
    refine ⟨54776089698019149381039623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146069572528051065016105661 54776089698019149381039623)
    ·
      refine ⟨82164134547028724071559435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54776089698019149381039623 82164134547028724071559435)
      ·
        refine ⟨123246201820543086107339153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82164134547028724071559435 123246201820543086107339153)
        ·
          refine ⟨92434651365407314580504365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123246201820543086107339153 92434651365407314580504365)
          ·
            refine ⟨34662994262027742967689137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92434651365407314580504365 34662994262027742967689137)
            ·
              refine ⟨25997245696520807225766853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34662994262027742967689137 25997245696520807225766853)
              ·
                refine ⟨4874483568097651354831285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25997245696520807225766853 4874483568097651354831285)
                ·
                  refine ⟨456982834509154814515433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4874483568097651354831285 456982834509154814515433)
                  ·
                    rfl

theorem cell22_4004869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_4004869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004869 prefixEnd_4004869 := by exact prefixLift 4004869
  have htrace : WordTrace (prefixWord ++ tailWord_4004869) baseStart_4004869 baseEnd_4004869 := by
    simpa [prefixWord, tailWord_4004869, baseEnd_4004869] using wordTrace_append hprefix tailTrace_4004869
  have hstable : (prefixWord ++ tailWord_4004869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004869).length < 2 ^ (prefixWord ++ tailWord_4004869).sum := by decide
  have hdescent : baseEnd_4004869 < baseStart_4004869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004931 : List Nat := [1, 1, 1, 3, 1, 2, 5, 4, 4]
def baseStart_4004931 : Nat := 118140960795 + 4004931 * 2 ^ 59
def prefixEnd_4004931 : Nat := 4983230072969 + 3 ^ 40 * 4004931 * 2
def baseEnd_4004931 : Nat := 456989909131505649498703

theorem tailTrace_4004931 : CollatzResearch.WordTrace tailWord_4004931 prefixEnd_4004931 456989909131505649498703 := by
  unfold tailWord_4004931
  simp only [CollatzResearch.WordTrace]
  refine ⟨146071833853826449604862647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97381222569217633069908431 146071833853826449604862647)
  ·
    refine ⟨219107750780739674407293971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146071833853826449604862647 219107750780739674407293971)
    ·
      refine ⟨328661626171109511610940957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219107750780739674407293971 328661626171109511610940957)
      ·
        refine ⟨123248109814166066854102859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328661626171109511610940957 123248109814166066854102859)
        ·
          refine ⟨184872164721249100281154289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123248109814166066854102859 184872164721249100281154289)
          ·
            refine ⟨138654123540936825210865717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184872164721249100281154289 138654123540936825210865717)
            ·
              refine ⟨12998824081962827363518661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138654123540936825210865717 12998824081962827363518661)
              ·
                refine ⟨2437279515368030130659749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12998824081962827363518661 2437279515368030130659749)
                ·
                  refine ⟨456989909131505649498703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2437279515368030130659749 456989909131505649498703)
                  ·
                    rfl

theorem cell22_4004931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 4].length) (baseStart_4004931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004931 prefixEnd_4004931 := by exact prefixLift 4004931
  have htrace : WordTrace (prefixWord ++ tailWord_4004931) baseStart_4004931 baseEnd_4004931 := by
    simpa [prefixWord, tailWord_4004931, baseEnd_4004931] using wordTrace_append hprefix tailTrace_4004931
  have hstable : (prefixWord ++ tailWord_4004931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004931).length < 2 ^ (prefixWord ++ tailWord_4004931).sum := by decide
  have hdescent : baseEnd_4004931 < baseStart_4004931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004944 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 4, 4]
def baseStart_4004944 : Nat := 118140960795 + 4004944 * 2 ^ 59
def prefixEnd_4004944 : Nat := 4983230072969 + 3 ^ 40 * 4004944 * 2
def baseEnd_4004944 : Nat := 1370974177560189247921069

theorem tailTrace_4004944 : CollatzResearch.WordTrace tailWord_4004944 prefixEnd_4004944 1370974177560189247921069 := by
  unfold tailWord_4004944
  simp only [CollatzResearch.WordTrace]
  refine ⟨73036154001389676412542943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97381538668519568550057257 73036154001389676412542943)
  ·
    refine ⟨109554231002084514618814415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73036154001389676412542943 109554231002084514618814415)
    ·
      refine ⟨164331346503126771928221623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109554231002084514618814415 164331346503126771928221623)
      ·
        refine ⟨246497019754690157892332435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164331346503126771928221623 246497019754690157892332435)
        ·
          refine ⟨369745529632035236838498653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246497019754690157892332435 369745529632035236838498653)
          ·
            refine ⟨138654573612013213814436995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369745529632035236838498653 138654573612013213814436995)
            ·
              refine ⟨207981860418019820721655493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138654573612013213814436995 207981860418019820721655493)
              ·
                refine ⟨38996598828378716385310405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207981860418019820721655493 38996598828378716385310405)
                ·
                  refine ⟨7311862280321009322245701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38996598828378716385310405 7311862280321009322245701)
                  ·
                    refine ⟨1370974177560189247921069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7311862280321009322245701 1370974177560189247921069)
                    ·
                      rfl

theorem cell22_4004944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_4004944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004944 prefixEnd_4004944 := by exact prefixLift 4004944
  have htrace : WordTrace (prefixWord ++ tailWord_4004944) baseStart_4004944 baseEnd_4004944 := by
    simpa [prefixWord, tailWord_4004944, baseEnd_4004944] using wordTrace_append hprefix tailTrace_4004944
  have hstable : (prefixWord ++ tailWord_4004944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004944).length < 2 ^ (prefixWord ++ tailWord_4004944).sum := by decide
  have hdescent : baseEnd_4004944 < baseStart_4004944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004946 : List Nat := [3, 2, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_4004946 : Nat := 118140960795 + 4004946 * 2 ^ 59
def prefixEnd_4004946 : Nat := 4983230072969 + 3 ^ 40 * 4004946 * 2
def baseEnd_4004946 : Nat := 1370974862201061909371063

theorem tailTrace_4004946 : CollatzResearch.WordTrace tailWord_4004946 prefixEnd_4004946 1370974862201061909371063 := by
  unfold tailWord_4004946
  simp only [CollatzResearch.WordTrace]
  refine ⟨36518095237193026791664673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97381587299181404777772461 36518095237193026791664673)
  ·
    refine ⟨27388571427894770093748505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36518095237193026791664673 27388571427894770093748505)
    ·
      refine ⟨20541428570921077570311379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27388571427894770093748505 20541428570921077570311379)
      ·
        refine ⟨30812142856381616355467069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20541428570921077570311379 30812142856381616355467069)
        ·
          refine ⟨11554553571143106133300151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30812142856381616355467069 11554553571143106133300151)
          ·
            refine ⟨17331830356714659199950227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11554553571143106133300151 17331830356714659199950227)
            ·
              refine ⟨25997745535071988799925341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17331830356714659199950227 25997745535071988799925341)
              ·
                refine ⟨9749154575651995799972003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25997745535071988799925341 9749154575651995799972003)
                ·
                  refine ⟨14623731863477993699958005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9749154575651995799972003 14623731863477993699958005)
                  ·
                    refine ⟨1370974862201061909371063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14623731863477993699958005 1370974862201061909371063)
                    ·
                      rfl

theorem cell22_4004946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_4004946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004946 prefixEnd_4004946 := by exact prefixLift 4004946
  have htrace : WordTrace (prefixWord ++ tailWord_4004946) baseStart_4004946 baseEnd_4004946 := by
    simpa [prefixWord, tailWord_4004946, baseEnd_4004946] using wordTrace_append hprefix tailTrace_4004946
  have hstable : (prefixWord ++ tailWord_4004946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004946).length < 2 ^ (prefixWord ++ tailWord_4004946).sum := by decide
  have hdescent : baseEnd_4004946 < baseStart_4004946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004961 : List Nat := [1, 2, 3, 1, 1, 2, 5, 1, 2, 4]
def baseStart_4004961 : Nat := 118140960795 + 4004961 * 2 ^ 59
def prefixEnd_4004961 : Nat := 4983230072969 + 3 ^ 40 * 4004961 * 2
def baseEnd_4004961 : Nat := 1370979997007606870246017

theorem tailTrace_4004961 : CollatzResearch.WordTrace tailWord_4004961 prefixEnd_4004961 1370979997007606870246017 := by
  unfold tailWord_4004961
  simp only [CollatzResearch.WordTrace]
  refine ⟨146072928043717764728454737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97381952029145176485636491 146072928043717764728454737)
  ·
    refine ⟨109554696032788323546341053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146072928043717764728454737 109554696032788323546341053)
    ·
      refine ⟨41083011012295621329877895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109554696032788323546341053 41083011012295621329877895)
      ·
        refine ⟨61624516518443431994816843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41083011012295621329877895 61624516518443431994816843)
        ·
          refine ⟨92436774777665147992225265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61624516518443431994816843 92436774777665147992225265)
          ·
            refine ⟨69327581083248860994168949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92436774777665147992225265 69327581083248860994168949)
            ·
              refine ⟨6499460726554580718203339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69327581083248860994168949 6499460726554580718203339)
              ·
                refine ⟨9749191089831871077305009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6499460726554580718203339 9749191089831871077305009)
                ·
                  refine ⟨7311893317373903307978757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9749191089831871077305009 7311893317373903307978757)
                  ·
                    refine ⟨1370979997007606870246017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7311893317373903307978757 1370979997007606870246017)
                    ·
                      rfl

theorem cell22_4004961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_4004961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4004961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4004961 prefixEnd_4004961 := by exact prefixLift 4004961
  have htrace : WordTrace (prefixWord ++ tailWord_4004961) baseStart_4004961 baseEnd_4004961 := by
    simpa [prefixWord, tailWord_4004961, baseEnd_4004961] using wordTrace_append hprefix tailTrace_4004961
  have hstable : (prefixWord ++ tailWord_4004961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004961).length < 2 ^ (prefixWord ++ tailWord_4004961).sum := by decide
  have hdescent : baseEnd_4004961 < baseStart_4004961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005019 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 6, 5]
def baseStart_4005019 : Nat := 118140960795 + 4005019 * 2 ^ 59
def prefixEnd_4005019 : Nat := 4983230072969 + 3 ^ 40 * 4005019 * 2
def baseEnd_4005019 : Nat := 1370999851592914052295839

theorem tailTrace_4005019 : CollatzResearch.WordTrace tailWord_4005019 prefixEnd_4005019 1370999851592914052295839 := by
  unfold tailWord_4005019
  simp only [CollatzResearch.WordTrace]
  refine ⟨146075043477507640634066111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97383362318338427089377407 146075043477507640634066111)
  ·
    refine ⟨219112565216261460951099167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146075043477507640634066111 219112565216261460951099167)
    ·
      refine ⟨328668847824392191426648751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219112565216261460951099167 328668847824392191426648751)
      ·
        refine ⟨493003271736588287139973127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328668847824392191426648751 493003271736588287139973127)
        ·
          refine ⟨739504907604882430709959691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493003271736588287139973127 739504907604882430709959691)
          ·
            refine ⟨1109257361407323646064939537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739504907604882430709959691 1109257361407323646064939537)
            ·
              refine ⟨831943021055492734548704653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1109257361407323646064939537 831943021055492734548704653)
              ·
                refine ⟨311978632895809775455764245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 831943021055492734548704653 311978632895809775455764245)
                ·
                  refine ⟨14623998416991083224488949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 311978632895809775455764245 14623998416991083224488949)
                  ·
                    refine ⟨1370999851592914052295839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14623998416991083224488949 1370999851592914052295839)
                    ·
                      rfl

theorem cell22_4005019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 5].length) (baseStart_4005019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005019 prefixEnd_4005019 := by exact prefixLift 4005019
  have htrace : WordTrace (prefixWord ++ tailWord_4005019) baseStart_4005019 baseEnd_4005019 := by
    simpa [prefixWord, tailWord_4005019, baseEnd_4005019] using wordTrace_append hprefix tailTrace_4005019
  have hstable : (prefixWord ++ tailWord_4005019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005019).length < 2 ^ (prefixWord ++ tailWord_4005019).sum := by decide
  have hdescent : baseEnd_4005019 < baseStart_4005019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005042 : List Nat := [3, 2, 1, 1, 1, 5, 3, 2, 1, 3]
def baseStart_4005042 : Nat := 118140960795 + 4005042 * 2 ^ 59
def prefixEnd_4005042 : Nat := 4983230072969 + 3 ^ 40 * 4005042 * 2
def baseEnd_4005042 : Nat := 1371007724962949658970769

theorem tailTrace_4005042 : CollatzResearch.WordTrace tailWord_4005042 prefixEnd_4005042 1371007724962949658970769 := by
  unfold tailWord_4005042
  simp only [CollatzResearch.WordTrace]
  refine ⟨36518970589106078890538345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97383921570949543708102253 36518970589106078890538345)
  ·
    refine ⟨27389227941829559167903759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36518970589106078890538345 27389227941829559167903759)
    ·
      refine ⟨41083841912744338751855639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27389227941829559167903759 41083841912744338751855639)
      ·
        refine ⟨61625762869116508127783459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41083841912744338751855639 61625762869116508127783459)
        ·
          refine ⟨92438644303674762191675189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61625762869116508127783459 92438644303674762191675189)
          ·
            refine ⟨8666122903469508955469549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92438644303674762191675189 8666122903469508955469549)
            ·
              refine ⟨3249796088801065858301081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8666122903469508955469549 3249796088801065858301081)
              ·
                refine ⟨2437347066600799393725811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3249796088801065858301081 2437347066600799393725811)
                ·
                  refine ⟨3656020599901199090588717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2437347066600799393725811 3656020599901199090588717)
                  ·
                    refine ⟨1371007724962949658970769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3656020599901199090588717 1371007724962949658970769)
                    ·
                      rfl

theorem cell22_4005042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_4005042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005042 prefixEnd_4005042 := by exact prefixLift 4005042
  have htrace : WordTrace (prefixWord ++ tailWord_4005042) baseStart_4005042 baseEnd_4005042 := by
    simpa [prefixWord, tailWord_4005042, baseEnd_4005042] using wordTrace_append hprefix tailTrace_4005042
  have hstable : (prefixWord ++ tailWord_4005042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005042).length < 2 ^ (prefixWord ++ tailWord_4005042).sum := by decide
  have hdescent : baseEnd_4005042 < baseStart_4005042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005100 : List Nat := [2, 2, 1, 1, 2, 4, 4, 2, 4]
def baseStart_4005100 : Nat := 118140960795 + 4005100 * 2 ^ 59
def prefixEnd_4005100 : Nat := 4983230072969 + 3 ^ 40 * 4005100 * 2
def baseEnd_4005100 : Nat := 457009193182752280340197

theorem tailTrace_4005100 : CollatzResearch.WordTrace tailWord_4005100 prefixEnd_4005100 457009193182752280340197 := by
  unfold tailWord_4005100
  simp only [CollatzResearch.WordTrace]
  refine ⟨73038998895107095733882377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97385331860142794311843169 73038998895107095733882377)
  ·
    refine ⟨54779249171330321800411783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73038998895107095733882377 54779249171330321800411783)
    ·
      refine ⟨82168873756995482700617675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54779249171330321800411783 82168873756995482700617675)
      ·
        refine ⟨123253310635493224050926513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82168873756995482700617675 123253310635493224050926513)
        ·
          refine ⟨92439982976619918038194885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123253310635493224050926513 92439982976619918038194885)
          ·
            refine ⟨17332496808116234632161541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92439982976619918038194885 17332496808116234632161541)
            ·
              refine ⟨3249843151521793993530289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17332496808116234632161541 3249843151521793993530289)
              ·
                refine ⟨2437382363641345495147717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3249843151521793993530289 2437382363641345495147717)
                ·
                  refine ⟨457009193182752280340197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2437382363641345495147717 457009193182752280340197)
                  ·
                    rfl

theorem cell22_4005100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_4005100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005100 prefixEnd_4005100 := by exact prefixLift 4005100
  have htrace : WordTrace (prefixWord ++ tailWord_4005100) baseStart_4005100 baseEnd_4005100 := by
    simpa [prefixWord, tailWord_4005100, baseEnd_4005100] using wordTrace_append hprefix tailTrace_4005100
  have hstable : (prefixWord ++ tailWord_4005100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005100).length < 2 ^ (prefixWord ++ tailWord_4005100).sum := by decide
  have hdescent : baseEnd_4005100 < baseStart_4005100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005143 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 5, 3]
def baseStart_4005143 : Nat := 118140960795 + 4005143 * 2 ^ 59
def prefixEnd_4005143 : Nat := 4983230072969 + 3 ^ 40 * 4005143 * 2
def baseEnd_4005143 : Nat := 1371042299327019062195459

theorem tailTrace_4005143 : CollatzResearch.WordTrace tailWord_4005143 prefixEnd_4005143 1371042299327019062195459 := by
  unfold tailWord_4005143
  simp only [CollatzResearch.WordTrace]
  refine ⟨146079566129058409811580083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97386377419372273207720055 146079566129058409811580083)
  ·
    refine ⟨219119349193587614717370125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146079566129058409811580083 219119349193587614717370125)
    ·
      refine ⟨82169755947595355519013797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219119349193587614717370125 82169755947595355519013797)
      ·
        refine ⟨15406829240174129159815087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82169755947595355519013797 15406829240174129159815087)
        ·
          refine ⟨23110243860261193739722631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15406829240174129159815087 23110243860261193739722631)
          ·
            refine ⟨34665365790391790609583947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23110243860261193739722631 34665365790391790609583947)
            ·
              refine ⟨51998048685587685914375921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34665365790391790609583947 51998048685587685914375921)
              ·
                refine ⟨38998536514190764435781941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51998048685587685914375921 38998536514190764435781941)
                ·
                  refine ⟨3656112798205384165854557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38998536514190764435781941 3656112798205384165854557)
                  ·
                    refine ⟨1371042299327019062195459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3656112798205384165854557 1371042299327019062195459)
                    ·
                      rfl

theorem cell22_4005143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_4005143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005143 prefixEnd_4005143 := by exact prefixLift 4005143
  have htrace : WordTrace (prefixWord ++ tailWord_4005143) baseStart_4005143 baseEnd_4005143 := by
    simpa [prefixWord, tailWord_4005143, baseEnd_4005143] using wordTrace_append hprefix tailTrace_4005143
  have hstable : (prefixWord ++ tailWord_4005143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005143).length < 2 ^ (prefixWord ++ tailWord_4005143).sum := by decide
  have hdescent : baseEnd_4005143 < baseStart_4005143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005160 : List Nat := [2, 1, 5, 1, 2, 1, 1, 3, 3, 3]
def baseStart_4005160 : Nat := 118140960795 + 4005160 * 2 ^ 59
def prefixEnd_4005160 : Nat := 4983230072969 + 3 ^ 40 * 4005160 * 2
def baseEnd_4005160 : Nat := 1371048118774436684520407

theorem tailTrace_4005160 : CollatzResearch.WordTrace tailWord_4005160 prefixEnd_4005160 1371048118774436684520407 := by
  unfold tailWord_4005160
  simp only [CollatzResearch.WordTrace]
  refine ⟨73040093084998410857474467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97386790779997881143299289 73040093084998410857474467)
  ·
    refine ⟨109560139627497616286211701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73040093084998410857474467 109560139627497616286211701)
    ·
      refine ⟨10271263090077901526832347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109560139627497616286211701 10271263090077901526832347)
      ·
        refine ⟨15406894635116852290248521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10271263090077901526832347 15406894635116852290248521)
        ·
          refine ⟨11555170976337639217686391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15406894635116852290248521 11555170976337639217686391)
          ·
            refine ⟨17332756464506458826529587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11555170976337639217686391 17332756464506458826529587)
            ·
              refine ⟨25999134696759688239794381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17332756464506458826529587 25999134696759688239794381)
              ·
                refine ⟨9749675511284883089922893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25999134696759688239794381 9749675511284883089922893)
                ·
                  refine ⟨3656128316731831158721085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9749675511284883089922893 3656128316731831158721085)
                  ·
                    refine ⟨1371048118774436684520407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3656128316731831158721085 1371048118774436684520407)
                    ·
                      rfl

theorem cell22_4005160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_4005160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005160 prefixEnd_4005160 := by exact prefixLift 4005160
  have htrace : WordTrace (prefixWord ++ tailWord_4005160) baseStart_4005160 baseEnd_4005160 := by
    simpa [prefixWord, tailWord_4005160, baseEnd_4005160] using wordTrace_append hprefix tailTrace_4005160
  have hstable : (prefixWord ++ tailWord_4005160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005160).length < 2 ^ (prefixWord ++ tailWord_4005160).sum := by decide
  have hdescent : baseEnd_4005160 < baseStart_4005160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005203 : List Nat := [1, 1, 1, 2, 1, 1, 5, 5, 1, 4]
def baseStart_4005203 : Nat := 118140960795 + 4005203 * 2 ^ 59
def prefixEnd_4005203 : Nat := 4983230072969 + 3 ^ 40 * 4005203 * 2
def baseEnd_4005203 : Nat := 1371062838553198905695275

theorem tailTrace_4005203 : CollatzResearch.WordTrace tailWord_4005203 prefixEnd_4005203 1371062838553198905695275 := by
  unfold tailWord_4005203
  simp only [CollatzResearch.WordTrace]
  refine ⟨146081754508841040058764263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97387836339227360039176175 146081754508841040058764263)
  ·
    refine ⟨219122631763261560088146395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146081754508841040058764263 219122631763261560088146395)
    ·
      refine ⟨328683947644892340132219593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219122631763261560088146395 328683947644892340132219593)
      ·
        refine ⟨246512960733669255099164695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328683947644892340132219593 246512960733669255099164695)
        ·
          refine ⟨369769441100503882648747043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246512960733669255099164695 369769441100503882648747043)
          ·
            refine ⟨554654161650755823973120565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369769441100503882648747043 554654161650755823973120565)
            ·
              refine ⟨51998827654758358497480053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 554654161650755823973120565 51998827654758358497480053)
              ·
                refine ⟨4874890092633596109138755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51998827654758358497480053 4874890092633596109138755)
                ·
                  refine ⟨7312335138950394163708133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4874890092633596109138755 7312335138950394163708133)
                  ·
                    refine ⟨1371062838553198905695275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7312335138950394163708133 1371062838553198905695275)
                    ·
                      rfl

theorem cell22_4005203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 4].length) (baseStart_4005203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005203 prefixEnd_4005203 := by exact prefixLift 4005203
  have htrace : WordTrace (prefixWord ++ tailWord_4005203) baseStart_4005203 baseEnd_4005203 := by
    simpa [prefixWord, tailWord_4005203, baseEnd_4005203] using wordTrace_append hprefix tailTrace_4005203
  have hstable : (prefixWord ++ tailWord_4005203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005203).length < 2 ^ (prefixWord ++ tailWord_4005203).sum := by decide
  have hdescent : baseEnd_4005203 < baseStart_4005203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005224 : List Nat := [2, 1, 4, 2, 4, 1, 2, 1, 5]
def baseStart_4005224 : Nat := 118140960795 + 4005224 * 2 ^ 59
def prefixEnd_4005224 : Nat := 4983230072969 + 3 ^ 40 * 4005224 * 2
def baseEnd_4005224 : Nat := 457023342427453950306737

theorem tailTrace_4005224 : CollatzResearch.WordTrace tailWord_4005224 prefixEnd_4005224 457023342427453950306737 := by
  unfold tailWord_4005224
  simp only [CollatzResearch.WordTrace]
  refine ⟨73041260220882480322639363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97388346961176640430185817 73041260220882480322639363)
  ·
    refine ⟨109561890331323720483959045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73041260220882480322639363 109561890331323720483959045)
    ·
      refine ⟨20542854437123197590742321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109561890331323720483959045 20542854437123197590742321)
      ·
        refine ⟨15407140827842398193056741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20542854437123197590742321 15407140827842398193056741)
        ·
          refine ⟨2888838905220449661198139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15407140827842398193056741 2888838905220449661198139)
          ·
            refine ⟨4333258357830674491797209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2888838905220449661198139 4333258357830674491797209)
            ·
              refine ⟨3249943768373005868847907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4333258357830674491797209 3249943768373005868847907)
              ·
                refine ⟨4874915652559508803271861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3249943768373005868847907 4874915652559508803271861)
                ·
                  refine ⟨457023342427453950306737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4874915652559508803271861 457023342427453950306737)
                  ·
                    rfl

theorem cell22_4005224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 5].length) (baseStart_4005224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005224 prefixEnd_4005224 := by exact prefixLift 4005224
  have htrace : WordTrace (prefixWord ++ tailWord_4005224) baseStart_4005224 baseEnd_4005224 := by
    simpa [prefixWord, tailWord_4005224, baseEnd_4005224] using wordTrace_append hprefix tailTrace_4005224
  have hstable : (prefixWord ++ tailWord_4005224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005224).length < 2 ^ (prefixWord ++ tailWord_4005224).sum := by decide
  have hdescent : baseEnd_4005224 < baseStart_4005224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005312 : List Nat := [2, 1, 1, 2, 3, 1, 3, 5, 1, 3]
def baseStart_4005312 : Nat := 118140960795 + 4005312 * 2 ^ 59
def prefixEnd_4005312 : Nat := 4983230072969 + 3 ^ 40 * 4005312 * 2
def baseEnd_4005312 : Nat := 1371100151480758954719941

theorem tailTrace_4005312 : CollatzResearch.WordTrace tailWord_4005312 prefixEnd_4005312 1371100151480758954719941 := by
  unfold tailWord_4005312
  simp only [CollatzResearch.WordTrace]
  refine ⟨73042865032723075837241095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97390486710297434449654793 73042865032723075837241095)
  ·
    refine ⟨109564297549084613755861643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73042865032723075837241095 109564297549084613755861643)
    ·
      refine ⟨164346446323626920633792465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109564297549084613755861643 164346446323626920633792465)
      ·
        refine ⟨123259834742720190475344349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164346446323626920633792465 123259834742720190475344349)
        ·
          refine ⟨46222438028520071428254131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123259834742720190475344349 46222438028520071428254131)
          ·
            refine ⟨69333657042780107142381197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46222438028520071428254131 69333657042780107142381197)
            ·
              refine ⟨26000121391042540178392949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69333657042780107142381197 26000121391042540178392949)
              ·
                refine ⟨2437511380410238141724339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26000121391042540178392949 2437511380410238141724339)
                ·
                  refine ⟨3656267070615357212586509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2437511380410238141724339 3656267070615357212586509)
                  ·
                    refine ⟨1371100151480758954719941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3656267070615357212586509 1371100151480758954719941)
                    ·
                      rfl

theorem cell22_4005312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 1, 3].length) (baseStart_4005312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005312 prefixEnd_4005312 := by exact prefixLift 4005312
  have htrace : WordTrace (prefixWord ++ tailWord_4005312) baseStart_4005312 baseEnd_4005312 := by
    simpa [prefixWord, tailWord_4005312, baseEnd_4005312] using wordTrace_append hprefix tailTrace_4005312
  have hstable : (prefixWord ++ tailWord_4005312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005312).length < 2 ^ (prefixWord ++ tailWord_4005312).sum := by decide
  have hdescent : baseEnd_4005312 < baseStart_4005312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005323 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 2, 5]
def baseStart_4005323 : Nat := 118140960795 + 4005323 * 2 ^ 59
def prefixEnd_4005323 : Nat := 4983230072969 + 3 ^ 40 * 4005323 * 2
def baseEnd_4005323 : Nat := 1371103917005558592694907

theorem tailTrace_4005323 : CollatzResearch.WordTrace tailWord_4005323 prefixEnd_4005323 1371103917005558592694907 := by
  unfold tailWord_4005323
  simp only [CollatzResearch.WordTrace]
  refine ⟨146086131268406300553132623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97390754178937533702088415 146086131268406300553132623)
  ·
    refine ⟨219129196902609450829698935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146086131268406300553132623 219129196902609450829698935)
    ·
      refine ⟨328693795353914176244548403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219129196902609450829698935 328693795353914176244548403)
      ·
        refine ⟨493040693030871264366822605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328693795353914176244548403 493040693030871264366822605)
        ·
          refine ⟨184890259886576724137558477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493040693030871264366822605 184890259886576724137558477)
          ·
            refine ⟨69333847457466271551584429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184890259886576724137558477 69333847457466271551584429)
            ·
              refine ⟨26000192796549851831844161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69333847457466271551584429 26000192796549851831844161)
              ·
                refine ⟨19500144597412388873883121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26000192796549851831844161 19500144597412388873883121)
                ·
                  refine ⟨14625108448059291655412341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19500144597412388873883121 14625108448059291655412341)
                  ·
                    refine ⟨1371103917005558592694907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14625108448059291655412341 1371103917005558592694907)
                    ·
                      rfl

theorem cell22_4005323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 5].length) (baseStart_4005323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005323 prefixEnd_4005323 := by exact prefixLift 4005323
  have htrace : WordTrace (prefixWord ++ tailWord_4005323) baseStart_4005323 baseEnd_4005323 := by
    simpa [prefixWord, tailWord_4005323, baseEnd_4005323] using wordTrace_append hprefix tailTrace_4005323
  have hstable : (prefixWord ++ tailWord_4005323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005323).length < 2 ^ (prefixWord ++ tailWord_4005323).sum := by decide
  have hdescent : baseEnd_4005323 < baseStart_4005323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005385 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 4, 3]
def baseStart_4005385 : Nat := 118140960795 + 4005385 * 2 ^ 59
def prefixEnd_4005385 : Nat := 4983230072969 + 3 ^ 40 * 4005385 * 2
def baseEnd_4005385 : Nat := 1371125140872611097644717

theorem tailTrace_4005385 : CollatzResearch.WordTrace tailWord_4005385 prefixEnd_4005385 1371125140872611097644717 := by
  unfold tailWord_4005385
  simp only [CollatzResearch.WordTrace]
  refine ⟨146088392594181685141889609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97392261729454456761259739 146088392594181685141889609)
  ·
    refine ⟨109566294445636263856417207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146088392594181685141889609 109566294445636263856417207)
    ·
      refine ⟨164349441668454395784625811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109566294445636263856417207 164349441668454395784625811)
      ·
        refine ⟨246524162502681593676938717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164349441668454395784625811 246524162502681593676938717)
        ·
          refine ⟨92446560938505597628852019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246524162502681593676938717 92446560938505597628852019)
          ·
            refine ⟨138669841407758396443278029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92446560938505597628852019 138669841407758396443278029)
            ·
              refine ⟨52001190527909398666229261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138669841407758396443278029 52001190527909398666229261)
              ·
                refine ⟨19500446447966024499835973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52001190527909398666229261 19500446447966024499835973)
                ·
                  refine ⟨3656333708993629593719245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19500446447966024499835973 3656333708993629593719245)
                  ·
                    refine ⟨1371125140872611097644717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3656333708993629593719245 1371125140872611097644717)
                    ·
                      rfl

theorem cell22_4005385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 3].length) (baseStart_4005385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005385 prefixEnd_4005385 := by exact prefixLift 4005385
  have htrace : WordTrace (prefixWord ++ tailWord_4005385) baseStart_4005385 baseEnd_4005385 := by
    simpa [prefixWord, tailWord_4005385, baseEnd_4005385] using wordTrace_append hprefix tailTrace_4005385
  have hstable : (prefixWord ++ tailWord_4005385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005385).length < 2 ^ (prefixWord ++ tailWord_4005385).sum := by decide
  have hdescent : baseEnd_4005385 < baseStart_4005385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005387 : List Nat := [1, 1, 1, 1, 8, 2, 1, 1, 6]
def baseStart_4005387 : Nat := 118140960795 + 4005387 * 2 ^ 59
def prefixEnd_4005387 : Nat := 4983230072969 + 3 ^ 40 * 4005387 * 2
def baseEnd_4005387 : Nat := 457041941837827919698237

theorem tailTrace_4005387 : CollatzResearch.WordTrace tailWord_4005387 prefixEnd_4005387 457041941837827919698237 := by
  unfold tailWord_4005387
  simp only [CollatzResearch.WordTrace]
  refine ⟨146088465540174439483462415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97392310360116292988974943 146088465540174439483462415)
  ·
    refine ⟨219132698310261659225193623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146088465540174439483462415 219132698310261659225193623)
    ·
      refine ⟨328699047465392488837790435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219132698310261659225193623 328699047465392488837790435)
      ·
        refine ⟨493048571198088733256685653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328699047465392488837790435 493048571198088733256685653)
        ·
          refine ⟨5777912943727602342851785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 493048571198088733256685653 5777912943727602342851785)
          ·
            refine ⟨4333434707795701757138839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5777912943727602342851785 4333434707795701757138839)
            ·
              refine ⟨6500152061693552635708259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4333434707795701757138839 6500152061693552635708259)
              ·
                refine ⟨9750228092540328953562389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6500152061693552635708259 9750228092540328953562389)
                ·
                  refine ⟨457041941837827919698237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9750228092540328953562389 457041941837827919698237)
                  ·
                    rfl

theorem cell22_4005387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 6].length) (baseStart_4005387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005387 prefixEnd_4005387 := by exact prefixLift 4005387
  have htrace : WordTrace (prefixWord ++ tailWord_4005387) baseStart_4005387 baseEnd_4005387 := by
    simpa [prefixWord, tailWord_4005387, baseEnd_4005387] using wordTrace_append hprefix tailTrace_4005387
  have hstable : (prefixWord ++ tailWord_4005387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005387).length < 2 ^ (prefixWord ++ tailWord_4005387).sum := by decide
  have hdescent : baseEnd_4005387 < baseStart_4005387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005494 : List Nat := [5, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_4005494 : Nat := 118140960795 + 4005494 * 2 ^ 59
def prefixEnd_4005494 : Nat := 4983230072969 + 3 ^ 40 * 4005494 * 2
def baseEnd_4005494 : Nat := 457054151266723715556461

theorem tailTrace_4005494 : CollatzResearch.WordTrace tailWord_4005494 prefixEnd_4005494 457054151266723715556461 := by
  unfold tailWord_4005494
  simp only [CollatzResearch.WordTrace]
  refine ⟨9130773009424174797350471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97394912100524531171738357 9130773009424174797350471)
  ·
    refine ⟨13696159514136262196025707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9130773009424174797350471 13696159514136262196025707)
    ·
      refine ⟨20544239271204393294038561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13696159514136262196025707 20544239271204393294038561)
      ·
        refine ⟨15408179453403294970528921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20544239271204393294038561 15408179453403294970528921)
        ·
          refine ⟨11556134590052471227896691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15408179453403294970528921 11556134590052471227896691)
          ·
            refine ⟨17334201885078706841845037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11556134590052471227896691 17334201885078706841845037)
            ·
              refine ⟨6500325706904515065691889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17334201885078706841845037 6500325706904515065691889)
              ·
                refine ⟨4875244280178386299268917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6500325706904515065691889 4875244280178386299268917)
                ·
                  refine ⟨457054151266723715556461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4875244280178386299268917 457054151266723715556461)
                  ·
                    rfl

theorem cell22_4005494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_4005494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005494 prefixEnd_4005494 := by exact prefixLift 4005494
  have htrace : WordTrace (prefixWord ++ tailWord_4005494) baseStart_4005494 baseEnd_4005494 := by
    simpa [prefixWord, tailWord_4005494, baseEnd_4005494] using wordTrace_append hprefix tailTrace_4005494
  have hstable : (prefixWord ++ tailWord_4005494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005494).length < 2 ^ (prefixWord ++ tailWord_4005494).sum := by decide
  have hdescent : baseEnd_4005494 < baseStart_4005494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005612 : List Nat := [2, 2, 1, 1, 2, 2, 3, 4, 5]
def baseStart_4005612 : Nat := 118140960795 + 4005612 * 2 ^ 59
def prefixEnd_4005612 : Nat := 4983230072969 + 3 ^ 40 * 4005612 * 2
def baseEnd_4005612 : Nat := 457067615870552724073007

theorem tailTrace_4005612 : CollatzResearch.WordTrace tailWord_4005612 prefixEnd_4005612 457067615870552724073007 := by
  unfold tailWord_4005612
  simp only [CollatzResearch.WordTrace]
  refine ⟨73048335982179651455201545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97397781309572868606935393 73048335982179651455201545)
  ·
    refine ⟨54786251986634738591401159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73048335982179651455201545 54786251986634738591401159)
    ·
      refine ⟨82179377979952107887101739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54786251986634738591401159 82179377979952107887101739)
      ·
        refine ⟨123269066969928161830652609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82179377979952107887101739 123269066969928161830652609)
        ·
          refine ⟨92451800227446121372989457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123269066969928161830652609 92451800227446121372989457)
          ·
            refine ⟨69338850170584591029742093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92451800227446121372989457 69338850170584591029742093)
            ·
              refine ⟨26002068813969221636153285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69338850170584591029742093 26002068813969221636153285)
              ·
                refine ⟨4875387902619229056778741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26002068813969221636153285 4875387902619229056778741)
                ·
                  refine ⟨457067615870552724073007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4875387902619229056778741 457067615870552724073007)
                  ·
                    rfl

theorem cell22_4005612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_4005612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005612 prefixEnd_4005612 := by exact prefixLift 4005612
  have htrace : WordTrace (prefixWord ++ tailWord_4005612) baseStart_4005612 baseEnd_4005612 := by
    simpa [prefixWord, tailWord_4005612, baseEnd_4005612] using wordTrace_append hprefix tailTrace_4005612
  have hstable : (prefixWord ++ tailWord_4005612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005612).length < 2 ^ (prefixWord ++ tailWord_4005612).sum := by decide
  have hdescent : baseEnd_4005612 < baseStart_4005612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005650 : List Nat := [3, 2, 4, 1, 1, 2, 2, 3, 1, 3]
def baseStart_4005650 : Nat := 118140960795 + 4005650 * 2 ^ 59
def prefixEnd_4005650 : Nat := 4983230072969 + 3 ^ 40 * 4005650 * 2
def baseEnd_4005650 : Nat := 1371215855788238739768905

theorem tailTrace_4005650 : CollatzResearch.WordTrace tailWord_4005650 prefixEnd_4005650 1371215855788238739768905 := by
  unfold tailWord_4005650
  simp only [CollatzResearch.WordTrace]
  refine ⟨36524514484555408850071601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97398705292147756933524269 36524514484555408850071601)
  ·
    refine ⟨27393385863416556637553701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36524514484555408850071601 27393385863416556637553701)
    ·
      refine ⟨5136259849390604369541319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27393385863416556637553701 5136259849390604369541319)
      ·
        refine ⟨7704389774085906554311979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5136259849390604369541319 7704389774085906554311979)
        ·
          refine ⟨11556584661128859831467969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7704389774085906554311979 11556584661128859831467969)
          ·
            refine ⟨8667438495846644873600977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11556584661128859831467969 8667438495846644873600977)
            ·
              refine ⟨6500578871884983655200733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8667438495846644873600977 6500578871884983655200733)
              ·
                refine ⟨2437717076956868870700275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6500578871884983655200733 2437717076956868870700275)
                ·
                  refine ⟨3656575615435303306050413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2437717076956868870700275 3656575615435303306050413)
                  ·
                    refine ⟨1371215855788238739768905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3656575615435303306050413 1371215855788238739768905)
                    ·
                      rfl

theorem cell22_4005650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_4005650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005650 prefixEnd_4005650 := by exact prefixLift 4005650
  have htrace : WordTrace (prefixWord ++ tailWord_4005650) baseStart_4005650 baseEnd_4005650 := by
    simpa [prefixWord, tailWord_4005650, baseEnd_4005650] using wordTrace_append hprefix tailTrace_4005650
  have hstable : (prefixWord ++ tailWord_4005650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005650).length < 2 ^ (prefixWord ++ tailWord_4005650).sum := by decide
  have hdescent : baseEnd_4005650 < baseStart_4005650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005687 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 6, 4]
def baseStart_4005687 : Nat := 118140960795 + 4005687 * 2 ^ 59
def prefixEnd_4005687 : Nat := 4983230072969 + 3 ^ 40 * 4005687 * 2
def baseEnd_4005687 : Nat := 1371228521644382976593791

theorem tailTrace_4005687 : CollatzResearch.WordTrace tailWord_4005687 prefixEnd_4005687 1371228521644382976593791 := by
  unfold tailWord_4005687
  simp only [CollatzResearch.WordTrace]
  refine ⟨146099407439087590719383315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97399604959391727146255543 146099407439087590719383315)
  ·
    refine ⟨219149111158631386079074973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146099407439087590719383315 219149111158631386079074973)
    ·
      refine ⟨82180916684486769779653115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219149111158631386079074973 82180916684486769779653115)
      ·
        refine ⟨123271375026730154669479673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82180916684486769779653115 123271375026730154669479673)
        ·
          refine ⟨92453531270047616002109755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123271375026730154669479673 92453531270047616002109755)
          ·
            refine ⟨138680296905071424003164633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92453531270047616002109755 138680296905071424003164633)
            ·
              refine ⟨104010222678803568002373475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138680296905071424003164633 104010222678803568002373475)
              ·
                refine ⟨156015334018205352003560213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104010222678803568002373475 156015334018205352003560213)
                ·
                  refine ⟨7313218782103375875166885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156015334018205352003560213 7313218782103375875166885)
                  ·
                    refine ⟨1371228521644382976593791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7313218782103375875166885 1371228521644382976593791)
                    ·
                      rfl

theorem cell22_4005687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_4005687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005687 prefixEnd_4005687 := by exact prefixLift 4005687
  have htrace : WordTrace (prefixWord ++ tailWord_4005687) baseStart_4005687 baseEnd_4005687 := by
    simpa [prefixWord, tailWord_4005687, baseEnd_4005687] using wordTrace_append hprefix tailTrace_4005687
  have hstable : (prefixWord ++ tailWord_4005687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005687).length < 2 ^ (prefixWord ++ tailWord_4005687).sum := by decide
  have hdescent : baseEnd_4005687 < baseStart_4005687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005708 : List Nat := [2, 2, 1, 3, 4, 2, 1, 3, 4]
def baseStart_4005708 : Nat := 118140960795 + 4005708 * 2 ^ 59
def prefixEnd_4005708 : Nat := 4983230072969 + 3 ^ 40 * 4005708 * 2
def baseEnd_4005708 : Nat := 457078570124515307272909

theorem tailTrace_4005708 : CollatzResearch.WordTrace tailWord_4005708 prefixEnd_4005708 457078570124515307272909 := by
  unfold tailWord_4005708
  simp only [CollatzResearch.WordTrace]
  refine ⟨73050086686005755652948889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97400115581341007537265185 73050086686005755652948889)
  ·
    refine ⟨54787565014504316739711667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73050086686005755652948889 54787565014504316739711667)
    ·
      refine ⟨82181347521756475109567501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54787565014504316739711667 82181347521756475109567501)
      ·
        refine ⟨30818005320658678166087813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82181347521756475109567501 30818005320658678166087813)
        ·
          refine ⟨5778375997623502156141465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30818005320658678166087813 5778375997623502156141465)
          ·
            refine ⟨4333781998217626617106099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5778375997623502156141465 4333781998217626617106099)
            ·
              refine ⟨6500672997326439925659149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4333781998217626617106099 6500672997326439925659149)
              ·
                refine ⟨2437752373997414972122181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6500672997326439925659149 2437752373997414972122181)
                ·
                  refine ⟨457078570124515307272909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2437752373997414972122181 457078570124515307272909)
                  ·
                    rfl

theorem cell22_4005708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_4005708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005708 prefixEnd_4005708 := by exact prefixLift 4005708
  have htrace : WordTrace (prefixWord ++ tailWord_4005708) baseStart_4005708 baseEnd_4005708 := by
    simpa [prefixWord, tailWord_4005708, baseEnd_4005708] using wordTrace_append hprefix tailTrace_4005708
  have hstable : (prefixWord ++ tailWord_4005708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005708).length < 2 ^ (prefixWord ++ tailWord_4005708).sum := by decide
  have hdescent : baseEnd_4005708 < baseStart_4005708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005719 : List Nat := [1, 1, 3, 2, 5, 2, 8]
def baseStart_4005719 : Nat := 118140960795 + 4005719 * 2 ^ 59
def prefixEnd_4005719 : Nat := 4983230072969 + 3 ^ 40 * 4005719 * 2
def baseEnd_4005719 : Nat := 50786647255494279992359

theorem tailTrace_4005719 : CollatzResearch.WordTrace tailWord_4005719 prefixEnd_4005719 50786647255494279992359 := by
  unfold tailWord_4005719
  simp only [CollatzResearch.WordTrace]
  refine ⟨146100574574971660184548211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97400383049981106789698807 146100574574971660184548211)
  ·
    refine ⟨219150861862457490276822317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146100574574971660184548211 219150861862457490276822317)
    ·
      refine ⟨82181573198421558853808369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219150861862457490276822317 82181573198421558853808369)
      ·
        refine ⟨61636179898816169140356277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82181573198421558853808369 61636179898816169140356277)
        ·
          refine ⟨5778391865514015856908401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61636179898816169140356277 5778391865514015856908401)
          ·
            refine ⟨4333793899135511892681301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5778391865514015856908401 4333793899135511892681301)
            ·
              refine ⟨50786647255494279992359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4333793899135511892681301 50786647255494279992359)
              ·
                rfl

theorem cell22_4005719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 8].length) (baseStart_4005719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005719 prefixEnd_4005719 := by exact prefixLift 4005719
  have htrace : WordTrace (prefixWord ++ tailWord_4005719) baseStart_4005719 baseEnd_4005719 := by
    simpa [prefixWord, tailWord_4005719, baseEnd_4005719] using wordTrace_append hprefix tailTrace_4005719
  have hstable : (prefixWord ++ tailWord_4005719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005719).length < 2 ^ (prefixWord ++ tailWord_4005719).sum := by decide
  have hdescent : baseEnd_4005719 < baseStart_4005719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005809 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 8]
def baseStart_4005809 : Nat := 118140960795 + 4005809 * 2 ^ 59
def prefixEnd_4005809 : Nat := 4983230072969 + 3 ^ 40 * 4005809 * 2
def baseEnd_4005809 : Nat := 457090094912538441681139

theorem tailTrace_4005809 : CollatzResearch.WordTrace tailWord_4005809 prefixEnd_4005809 457090094912538441681139 := by
  unfold tailWord_4005809
  simp only [CollatzResearch.WordTrace]
  refine ⟨146103857144645605555324481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97402571429763737036882987 146103857144645605555324481)
  ·
    refine ⟨109577892858484204166493361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146103857144645605555324481 109577892858484204166493361)
    ·
      refine ⟨82183419643863153124870021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109577892858484204166493361 82183419643863153124870021)
      ·
        refine ⟨15409391183224341210913129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82183419643863153124870021 15409391183224341210913129)
        ·
          refine ⟨11557043387418255908184847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15409391183224341210913129 11557043387418255908184847)
          ·
            refine ⟨17335565081127383862277271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11557043387418255908184847 17335565081127383862277271)
            ·
              refine ⟨26003347621691075793415907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17335565081127383862277271 26003347621691075793415907)
              ·
                refine ⟨39005021432536613690123861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26003347621691075793415907 39005021432536613690123861)
                ·
                  refine ⟨457090094912538441681139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39005021432536613690123861 457090094912538441681139)
                  ·
                    rfl

theorem cell22_4005809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 8].length) (baseStart_4005809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005809 prefixEnd_4005809 := by exact prefixLift 4005809
  have htrace : WordTrace (prefixWord ++ tailWord_4005809) baseStart_4005809 baseEnd_4005809 := by
    simpa [prefixWord, tailWord_4005809, baseEnd_4005809] using wordTrace_append hprefix tailTrace_4005809
  have hstable : (prefixWord ++ tailWord_4005809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005809).length < 2 ^ (prefixWord ++ tailWord_4005809).sum := by decide
  have hdescent : baseEnd_4005809 < baseStart_4005809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005824 : List Nat := [2, 1, 1, 2, 3, 2, 1, 4, 1, 5]
def baseStart_4005824 : Nat := 118140960795 + 4005824 * 2 ^ 59
def prefixEnd_4005824 : Nat := 4983230072969 + 3 ^ 40 * 4005824 * 2
def baseEnd_4005824 : Nat := 1371275419544160285918371

theorem tailTrace_4005824 : CollatzResearch.WordTrace tailWord_4005824 prefixEnd_4005824 1371275419544160285918371 := by
  unfold tailWord_4005824
  simp only [CollatzResearch.WordTrace]
  refine ⟨73052202119795631558560263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97402936159727508744747017 73052202119795631558560263)
  ·
    refine ⟨109578303179693447337840395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73052202119795631558560263 109578303179693447337840395)
    ·
      refine ⟨164367454769540171006760593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109578303179693447337840395 164367454769540171006760593)
      ·
        refine ⟨123275591077155128255070445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164367454769540171006760593 123275591077155128255070445)
        ·
          refine ⟨46228346653933173095651417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123275591077155128255070445 46228346653933173095651417)
          ·
            refine ⟨34671259990449879821738563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46228346653933173095651417 34671259990449879821738563)
            ·
              refine ⟨52006889985674819732607845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34671259990449879821738563 52006889985674819732607845)
              ·
                refine ⟨9751291872314028699863971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52006889985674819732607845 9751291872314028699863971)
                ·
                  refine ⟨14626937808471043049795957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9751291872314028699863971 14626937808471043049795957)
                  ·
                    refine ⟨1371275419544160285918371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14626937808471043049795957 1371275419544160285918371)
                    ·
                      rfl

theorem cell22_4005824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_4005824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005824 prefixEnd_4005824 := by exact prefixLift 4005824
  have htrace : WordTrace (prefixWord ++ tailWord_4005824) baseStart_4005824 baseEnd_4005824 := by
    simpa [prefixWord, tailWord_4005824, baseEnd_4005824] using wordTrace_append hprefix tailTrace_4005824
  have hstable : (prefixWord ++ tailWord_4005824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005824).length < 2 ^ (prefixWord ++ tailWord_4005824).sum := by decide
  have hdescent : baseEnd_4005824 < baseStart_4005824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005839 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 4, 4]
def baseStart_4005839 : Nat := 118140960795 + 4005839 * 2 ^ 59
def prefixEnd_4005839 : Nat := 4983230072969 + 3 ^ 40 * 4005839 * 2
def baseEnd_4005839 : Nat := 1371280554350705246793325

theorem tailTrace_4005839 : CollatzResearch.WordTrace tailWord_4005839 prefixEnd_4005839 1371280554350705246793325 := by
  unfold tailWord_4005839
  simp only [CollatzResearch.WordTrace]
  refine ⟨146104951334536920678916571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97403300889691280452611047 146104951334536920678916571)
  ·
    refine ⟨219157427001805381018374857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146104951334536920678916571 219157427001805381018374857)
    ·
      refine ⟨164368070251354035763781143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219157427001805381018374857 164368070251354035763781143)
      ·
        refine ⟨246552105377031053645671715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164368070251354035763781143 246552105377031053645671715)
        ·
          refine ⟨369828158065546580468507573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246552105377031053645671715 369828158065546580468507573)
          ·
            refine ⟨34671389818644991918922585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 369828158065546580468507573 34671389818644991918922585)
            ·
              refine ⟨26003542363983743939191939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34671389818644991918922585 26003542363983743939191939)
              ·
                refine ⟨39005313545975615908787909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26003542363983743939191939 39005313545975615908787909)
                ·
                  refine ⟨7313496289870427982897733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39005313545975615908787909 7313496289870427982897733)
                  ·
                    refine ⟨1371280554350705246793325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7313496289870427982897733 1371280554350705246793325)
                    ·
                      rfl

theorem cell22_4005839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_4005839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005839 prefixEnd_4005839 := by exact prefixLift 4005839
  have htrace : WordTrace (prefixWord ++ tailWord_4005839) baseStart_4005839 baseEnd_4005839 := by
    simpa [prefixWord, tailWord_4005839, baseEnd_4005839] using wordTrace_append hprefix tailTrace_4005839
  have hstable : (prefixWord ++ tailWord_4005839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005839).length < 2 ^ (prefixWord ++ tailWord_4005839).sum := by decide
  have hdescent : baseEnd_4005839 < baseStart_4005839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005841 : List Nat := [1, 2, 2, 1, 2, 1, 2, 6, 2, 3]
def baseStart_4005841 : Nat := 118140960795 + 4005841 * 2 ^ 59
def prefixEnd_4005841 : Nat := 4983230072969 + 3 ^ 40 * 4005841 * 2
def baseEnd_4005841 : Nat := 1371281238991577908243319

theorem tailTrace_4005841 : CollatzResearch.WordTrace tailWord_4005841 prefixEnd_4005841 1371281238991577908243319 := by
  unfold tailWord_4005841
  simp only [CollatzResearch.WordTrace]
  refine ⟨146105024280529675020489377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97403349520353116680326251 146105024280529675020489377)
  ·
    refine ⟨109578768210397256265367033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146105024280529675020489377 109578768210397256265367033)
    ·
      refine ⟨82184076157797942199025275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109578768210397256265367033 82184076157797942199025275)
      ·
        refine ⟨123276114236696913298537913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82184076157797942199025275 123276114236696913298537913)
        ·
          refine ⟨92457085677522684973903435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123276114236696913298537913 92457085677522684973903435)
          ·
            refine ⟨138685628516284027460855153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92457085677522684973903435 138685628516284027460855153)
            ·
              refine ⟨104014221387213020595641365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138685628516284027460855153 104014221387213020595641365)
              ·
                refine ⟨4875666627525610340420689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104014221387213020595641365 4875666627525610340420689)
                ·
                  refine ⟨3656749970644207755315517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4875666627525610340420689 3656749970644207755315517)
                  ·
                    refine ⟨1371281238991577908243319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3656749970644207755315517 1371281238991577908243319)
                    ·
                      rfl

theorem cell22_4005841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_4005841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005841 prefixEnd_4005841 := by exact prefixLift 4005841
  have htrace : WordTrace (prefixWord ++ tailWord_4005841) baseStart_4005841 baseEnd_4005841 := by
    simpa [prefixWord, tailWord_4005841, baseEnd_4005841] using wordTrace_append hprefix tailTrace_4005841
  have hstable : (prefixWord ++ tailWord_4005841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005841).length < 2 ^ (prefixWord ++ tailWord_4005841).sum := by decide
  have hdescent : baseEnd_4005841 < baseStart_4005841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005894 : List Nat := [6, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_4005894 : Nat := 118140960795 + 4005894 * 2 ^ 59
def prefixEnd_4005894 : Nat := 4983230072969 + 3 ^ 40 * 4005894 * 2
def baseEnd_4005894 : Nat := 457099793991567812222719

theorem tailTrace_4005894 : CollatzResearch.WordTrace tailWord_4005894 prefixEnd_4005894 457099793991567812222719 := by
  unfold tailWord_4005894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4565842417166802033505273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97404638232891776714779157 4565842417166802033505273)
  ·
    refine ⟨3424381812875101525128955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4565842417166802033505273 3424381812875101525128955)
    ·
      refine ⟨5136572719312652287693433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3424381812875101525128955 5136572719312652287693433)
      ·
        refine ⟨3852429539484489215770075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5136572719312652287693433 3852429539484489215770075)
        ·
          refine ⟨5778644309226733823655113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3852429539484489215770075 5778644309226733823655113)
          ·
            refine ⟨4333983231920050367741335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5778644309226733823655113 4333983231920050367741335)
            ·
              refine ⟨6500974847880075551612003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4333983231920050367741335 6500974847880075551612003)
              ·
                refine ⟨9751462271820113327418005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6500974847880075551612003 9751462271820113327418005)
                ·
                  refine ⟨457099793991567812222719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9751462271820113327418005 457099793991567812222719)
                  ·
                    rfl

theorem cell22_4005894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_4005894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005894 prefixEnd_4005894 := by exact prefixLift 4005894
  have htrace : WordTrace (prefixWord ++ tailWord_4005894) baseStart_4005894 baseEnd_4005894 := by
    simpa [prefixWord, tailWord_4005894, baseEnd_4005894] using wordTrace_append hprefix tailTrace_4005894
  have hstable : (prefixWord ++ tailWord_4005894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005894).length < 2 ^ (prefixWord ++ tailWord_4005894).sum := by decide
  have hdescent : baseEnd_4005894 < baseStart_4005894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005899 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 7]
def baseStart_4005899 : Nat := 118140960795 + 4005899 * 2 ^ 59
def prefixEnd_4005899 : Nat := 4983230072969 + 3 ^ 40 * 4005899 * 2
def baseEnd_4005899 : Nat := 457100364525628363431047

theorem tailTrace_4005899 : CollatzResearch.WordTrace tailWord_4005899 prefixEnd_4005899 457100364525628363431047 := by
  unfold tailWord_4005899
  simp only [CollatzResearch.WordTrace]
  refine ⟨146107139714319550926100751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97404759809546367284067167 146107139714319550926100751)
  ·
    refine ⟨219160709571479326389151127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146107139714319550926100751 219160709571479326389151127)
    ·
      refine ⟨328741064357218989583726691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219160709571479326389151127 328741064357218989583726691)
      ·
        refine ⟨493111596535828484375590037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328741064357218989583726691 493111596535828484375590037)
        ·
          refine ⟨23114606087616960205105783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 493111596535828484375590037 23114606087616960205105783)
          ·
            refine ⟨34671909131425440307658675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23114606087616960205105783 34671909131425440307658675)
            ·
              refine ⟨52007863697138160461488013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34671909131425440307658675 52007863697138160461488013)
              ·
                refine ⟨19502948886426810173058005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52007863697138160461488013 19502948886426810173058005)
                ·
                  refine ⟨457100364525628363431047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19502948886426810173058005 457100364525628363431047)
                  ·
                    rfl

theorem cell22_4005899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 7].length) (baseStart_4005899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005899 prefixEnd_4005899 := by exact prefixLift 4005899
  have htrace : WordTrace (prefixWord ++ tailWord_4005899) baseStart_4005899 baseEnd_4005899 := by
    simpa [prefixWord, tailWord_4005899, baseEnd_4005899] using wordTrace_append hprefix tailTrace_4005899
  have hstable : (prefixWord ++ tailWord_4005899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005899).length < 2 ^ (prefixWord ++ tailWord_4005899).sum := by decide
  have hdescent : baseEnd_4005899 < baseStart_4005899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005950 : List Nat := [4, 2, 1, 3, 2, 1, 2, 2, 5]
def baseStart_4005950 : Nat := 118140960795 + 4005950 * 2 ^ 59
def prefixEnd_4005950 : Nat := 4983230072969 + 3 ^ 40 * 4005950 * 2
def baseEnd_4005950 : Nat := 457106183973045985755995

theorem tailTrace_4005950 : CollatzResearch.WordTrace tailWord_4005950 prefixEnd_4005950 457106183973045985755995 := by
  unfold tailWord_4005950
  simp only [CollatzResearch.WordTrace]
  refine ⟨18263624979641848329525913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97405999891423191090804869 18263624979641848329525913)
  ·
    refine ⟨13697718734731386247144435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18263624979641848329525913 13697718734731386247144435)
    ·
      refine ⟨20546578102097079370716653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13697718734731386247144435 20546578102097079370716653)
      ·
        refine ⟨7704966788286404764018745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20546578102097079370716653 7704966788286404764018745)
        ·
          refine ⟨5778725091214803573014059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7704966788286404764018745 5778725091214803573014059)
          ·
            refine ⟨8668087636822205359521089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5778725091214803573014059 8668087636822205359521089)
            ·
              refine ⟨6501065727616654019640817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8668087636822205359521089 6501065727616654019640817)
              ·
                refine ⟨4875799295712490514730613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6501065727616654019640817 4875799295712490514730613)
                ·
                  refine ⟨457106183973045985755995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4875799295712490514730613 457106183973045985755995)
                  ·
                    rfl

theorem cell22_4005950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_4005950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005950 prefixEnd_4005950 := by exact prefixLift 4005950
  have htrace : WordTrace (prefixWord ++ tailWord_4005950) baseStart_4005950 baseEnd_4005950 := by
    simpa [prefixWord, tailWord_4005950, baseEnd_4005950] using wordTrace_append hprefix tailTrace_4005950
  have hstable : (prefixWord ++ tailWord_4005950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005950).length < 2 ^ (prefixWord ++ tailWord_4005950).sum := by decide
  have hdescent : baseEnd_4005950 < baseStart_4005950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005976 : List Nat := [2, 1, 2, 2, 1, 4, 1, 3, 1, 5]
def baseStart_4005976 : Nat := 118140960795 + 4005976 * 2 ^ 59
def prefixEnd_4005976 : Nat := 4983230072969 + 3 ^ 40 * 4005976 * 2
def baseEnd_4005976 : Nat := 1371327452250482556117905

theorem tailTrace_4005976 : CollatzResearch.WordTrace tailWord_4005976 prefixEnd_4005976 1371327452250482556117905 := by
  unfold tailWord_4005976
  simp only [CollatzResearch.WordTrace]
  refine ⟨73054974067520296538326891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97406632090027062051102521 73054974067520296538326891)
  ·
    refine ⟨109582461101280444807490337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73054974067520296538326891 109582461101280444807490337)
    ·
      refine ⟨82186845825960333605617753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109582461101280444807490337 82186845825960333605617753)
      ·
        refine ⟨61640134369470250204213315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82186845825960333605617753 61640134369470250204213315)
        ·
          refine ⟨92460201554205375306319973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61640134369470250204213315 92460201554205375306319973)
          ·
            refine ⟨17336287791413507869934995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92460201554205375306319973 17336287791413507869934995)
            ·
              refine ⟨26004431687120261804902493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17336287791413507869934995 26004431687120261804902493)
              ·
                refine ⟨9751661882670098176838435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26004431687120261804902493 9751661882670098176838435)
                ·
                  refine ⟨14627492824005147265257653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9751661882670098176838435 14627492824005147265257653)
                  ·
                    refine ⟨1371327452250482556117905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14627492824005147265257653 1371327452250482556117905)
                    ·
                      rfl

theorem cell22_4005976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_4005976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005976 prefixEnd_4005976 := by exact prefixLift 4005976
  have htrace : WordTrace (prefixWord ++ tailWord_4005976) baseStart_4005976 baseEnd_4005976 := by
    simpa [prefixWord, tailWord_4005976, baseEnd_4005976] using wordTrace_append hprefix tailTrace_4005976
  have hstable : (prefixWord ++ tailWord_4005976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005976).length < 2 ^ (prefixWord ++ tailWord_4005976).sum := by decide
  have hdescent : baseEnd_4005976 < baseStart_4005976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005991 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 1, 6]
def baseStart_4005991 : Nat := 118140960795 + 4005991 * 2 ^ 59
def prefixEnd_4005991 : Nat := 4983230072969 + 3 ^ 40 * 4005991 * 2
def baseEnd_4005991 : Nat := 1371332587057027516992859

theorem tailTrace_4005991 : CollatzResearch.WordTrace tailWord_4005991 prefixEnd_4005991 1371332587057027516992859 := by
  unfold tailWord_4005991
  simp only [CollatzResearch.WordTrace]
  refine ⟨146110495229986250638449827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97406996819990833758966551 146110495229986250638449827)
  ·
    refine ⟨219165742844979375957674741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146110495229986250638449827 219165742844979375957674741)
    ·
      refine ⟨20546788391716816496032007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219165742844979375957674741 20546788391716816496032007)
      ·
        refine ⟨30820182587575224744048011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20546788391716816496032007 30820182587575224744048011)
        ·
          refine ⟨46230273881362837116072017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30820182587575224744048011 46230273881362837116072017)
          ·
            refine ⟨34672705411022127837054013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46230273881362837116072017 34672705411022127837054013)
            ·
              refine ⟨13002264529133297938895255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34672705411022127837054013 13002264529133297938895255)
              ·
                refine ⟨19503396793699946908342883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13002264529133297938895255 19503396793699946908342883)
                ·
                  refine ⟨29255095190549920362514325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19503396793699946908342883 29255095190549920362514325)
                  ·
                    refine ⟨1371332587057027516992859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29255095190549920362514325 1371332587057027516992859)
                    ·
                      rfl

theorem cell22_4005991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_4005991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4005991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4005991 prefixEnd_4005991 := by exact prefixLift 4005991
  have htrace : WordTrace (prefixWord ++ tailWord_4005991) baseStart_4005991 baseEnd_4005991 := by
    simpa [prefixWord, tailWord_4005991, baseEnd_4005991] using wordTrace_append hprefix tailTrace_4005991
  have hstable : (prefixWord ++ tailWord_4005991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005991).length < 2 ^ (prefixWord ++ tailWord_4005991).sum := by decide
  have hdescent : baseEnd_4005991 < baseStart_4005991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006040 : List Nat := [2, 1, 2, 4, 3, 2, 2, 6]
def baseStart_4006040 : Nat := 118140960795 + 4006040 * 2 ^ 59
def prefixEnd_4006040 : Nat := 4983230072969 + 3 ^ 40 * 4006040 * 2
def baseEnd_4006040 : Nat := 152372151195378635835301

theorem tailTrace_4006040 : CollatzResearch.WordTrace tailWord_4006040 prefixEnd_4006040 152372151195378635835301 := by
  unfold tailWord_4006040
  simp only [CollatzResearch.WordTrace]
  refine ⟨73056141203404366003491787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97408188271205821337989049 73056141203404366003491787)
  ·
    refine ⟨109584211805106549005237681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73056141203404366003491787 109584211805106549005237681)
    ·
      refine ⟨82188158853829911753928261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109584211805106549005237681 82188158853829911753928261)
      ·
        refine ⟨15410279785093108453861549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82188158853829911753928261 15410279785093108453861549)
        ·
          refine ⟨5778854919409915670198081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15410279785093108453861549 5778854919409915670198081)
          ·
            refine ⟨4334141189557436752648561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5778854919409915670198081 4334141189557436752648561)
            ·
              refine ⟨3250605892168077564486421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4334141189557436752648561 3250605892168077564486421)
              ·
                refine ⟨152372151195378635835301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3250605892168077564486421 152372151195378635835301)
                ·
                  rfl

theorem cell22_4006040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 6].length) (baseStart_4006040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006040 prefixEnd_4006040 := by exact prefixLift 4006040
  have htrace : WordTrace (prefixWord ++ tailWord_4006040) baseStart_4006040 baseEnd_4006040 := by
    simpa [prefixWord, tailWord_4006040, baseEnd_4006040] using wordTrace_append hprefix tailTrace_4006040
  have hstable : (prefixWord ++ tailWord_4006040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006040).length < 2 ^ (prefixWord ++ tailWord_4006040).sum := by decide
  have hdescent : baseEnd_4006040 < baseStart_4006040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006072 : List Nat := [2, 1, 2, 1, 2, 1, 7, 2, 1, 3]
def baseStart_4006072 : Nat := 118140960795 + 4006072 * 2 ^ 59
def prefixEnd_4006072 : Nat := 4983230072969 + 3 ^ 40 * 4006072 * 2
def baseEnd_4006072 : Nat := 1371360315012370305717611

theorem tailTrace_4006072 : CollatzResearch.WordTrace tailWord_4006072 prefixEnd_4006072 1371360315012370305717611 := by
  unfold tailWord_4006072
  simp only [CollatzResearch.WordTrace]
  refine ⟨73056724771346400736074235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97408966361795200981432313 73056724771346400736074235)
  ·
    refine ⟨109585087157019601104111353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73056724771346400736074235 109585087157019601104111353)
    ·
      refine ⟨82188815367764700828083515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109585087157019601104111353 82188815367764700828083515)
      ·
        refine ⟨123283223051647051242125273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82188815367764700828083515 123283223051647051242125273)
        ·
          refine ⟨92462417288735288431593955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123283223051647051242125273 92462417288735288431593955)
          ·
            refine ⟨138693625933102932647390933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92462417288735288431593955 138693625933102932647390933)
            ·
              refine ⟨3250631857807099983923225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 138693625933102932647390933 3250631857807099983923225)
              ·
                refine ⟨2437973893355324987942419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3250631857807099983923225 2437973893355324987942419)
                ·
                  refine ⟨3656960840032987481913629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2437973893355324987942419 3656960840032987481913629)
                  ·
                    refine ⟨1371360315012370305717611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3656960840032987481913629 1371360315012370305717611)
                    ·
                      rfl

theorem cell22_4006072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 1, 3].length) (baseStart_4006072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006072 prefixEnd_4006072 := by exact prefixLift 4006072
  have htrace : WordTrace (prefixWord ++ tailWord_4006072) baseStart_4006072 baseEnd_4006072 := by
    simpa [prefixWord, tailWord_4006072, baseEnd_4006072] using wordTrace_append hprefix tailTrace_4006072
  have hstable : (prefixWord ++ tailWord_4006072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006072).length < 2 ^ (prefixWord ++ tailWord_4006072).sum := by decide
  have hdescent : baseEnd_4006072 < baseStart_4006072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006128 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 4, 3]
def baseStart_4006128 : Nat := 118140960795 + 4006128 * 2 ^ 59
def prefixEnd_4006128 : Nat := 4983230072969 + 3 ^ 40 * 4006128 * 2
def baseEnd_4006128 : Nat := 1371379484956804826317439

theorem tailTrace_4006128 : CollatzResearch.WordTrace tailWord_4006128 prefixEnd_4006128 1371379484956804826317439 := by
  unfold tailWord_4006128
  simp only [CollatzResearch.WordTrace]
  refine ⟨73057746015244961518093519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97410328020326615357458025 73057746015244961518093519)
  ·
    refine ⟨109586619022867442277140279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73057746015244961518093519 109586619022867442277140279)
    ·
      refine ⟨164379928534301163415710419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109586619022867442277140279 164379928534301163415710419)
      ·
        refine ⟨246569892801451745123565629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164379928534301163415710419 246569892801451745123565629)
        ·
          refine ⟨92463709800544404421337111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246569892801451745123565629 92463709800544404421337111)
          ·
            refine ⟨138695564700816606632005667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92463709800544404421337111 138695564700816606632005667)
            ·
              refine ⟨208043347051224909948008501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138695564700816606632005667 208043347051224909948008501)
              ·
                refine ⟨19504063786052335307625797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208043347051224909948008501 19504063786052335307625797)
                ·
                  refine ⟨3657011959884812870179837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19504063786052335307625797 3657011959884812870179837)
                  ·
                    refine ⟨1371379484956804826317439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3657011959884812870179837 1371379484956804826317439)
                    ·
                      rfl

theorem cell22_4006128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 4, 3].length) (baseStart_4006128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006128 prefixEnd_4006128 := by exact prefixLift 4006128
  have htrace : WordTrace (prefixWord ++ tailWord_4006128) baseStart_4006128 baseEnd_4006128 := by
    simpa [prefixWord, tailWord_4006128, baseEnd_4006128] using wordTrace_append hprefix tailTrace_4006128
  have hstable : (prefixWord ++ tailWord_4006128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006128).length < 2 ^ (prefixWord ++ tailWord_4006128).sum := by decide
  have hdescent : baseEnd_4006128 < baseStart_4006128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006145 : List Nat := [1, 2, 4, 1, 1, 2, 1, 5, 2, 3]
def baseStart_4006145 : Nat := 118140960795 + 4006145 * 2 ^ 59
def prefixEnd_4006145 : Nat := 4983230072969 + 3 ^ 40 * 4006145 * 2
def baseEnd_4006145 : Nat := 1371385304404222448642387

theorem tailTrace_4006145 : CollatzResearch.WordTrace tailWord_4006145 prefixEnd_4006145 1371385304404222448642387 := by
  unfold tailWord_4006145
  simp only [CollatzResearch.WordTrace]
  refine ⟨146116112071428334939555889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97410741380952223293037259 146116112071428334939555889)
  ·
    refine ⟨109587084053571251204666917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146116112071428334939555889 109587084053571251204666917)
    ·
      refine ⟨20547578260044609600875047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109587084053571251204666917 20547578260044609600875047)
      ·
        refine ⟨30821367390066914401312571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20547578260044609600875047 30821367390066914401312571)
        ·
          refine ⟨46232051085100371601968857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30821367390066914401312571 46232051085100371601968857)
          ·
            refine ⟨34674038313825278701476643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46232051085100371601968857 34674038313825278701476643)
            ·
              refine ⟨52011057470737918052214965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34674038313825278701476643 52011057470737918052214965)
              ·
                refine ⟨4876036637881679817395153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52011057470737918052214965 4876036637881679817395153)
                ·
                  refine ⟨3657027478411259863046365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4876036637881679817395153 3657027478411259863046365)
                  ·
                    refine ⟨1371385304404222448642387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3657027478411259863046365 1371385304404222448642387)
                    ·
                      rfl

theorem cell22_4006145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_4006145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006145 prefixEnd_4006145 := by exact prefixLift 4006145
  have htrace : WordTrace (prefixWord ++ tailWord_4006145) baseStart_4006145 baseEnd_4006145 := by
    simpa [prefixWord, tailWord_4006145, baseEnd_4006145] using wordTrace_append hprefix tailTrace_4006145
  have hstable : (prefixWord ++ tailWord_4006145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006145).length < 2 ^ (prefixWord ++ tailWord_4006145).sum := by decide
  have hdescent : baseEnd_4006145 < baseStart_4006145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006209 : List Nat := [1, 2, 5, 2, 3, 1, 2, 6]
def baseStart_4006209 : Nat := 118140960795 + 4006209 * 2 ^ 59
def prefixEnd_4006209 : Nat := 4983230072969 + 3 ^ 40 * 4006209 * 2
def baseEnd_4006209 : Nat := 152378579212460846115799

theorem tailTrace_4006209 : CollatzResearch.WordTrace tailWord_4006209 prefixEnd_4006209 152378579212460846115799 := by
  unfold tailWord_4006209
  simp only [CollatzResearch.WordTrace]
  refine ⟨146118446343196473869885681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97412297562130982579923787 146118446343196473869885681)
  ·
    refine ⟨109588834757397355402414261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146118446343196473869885681 109588834757397355402414261)
    ·
      refine ⟨10273953258506002068976337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109588834757397355402414261 10273953258506002068976337)
      ·
        refine ⟨7705464943879501551732253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10273953258506002068976337 7705464943879501551732253)
        ·
          refine ⟨2889549353954813081899595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7705464943879501551732253 2889549353954813081899595)
          ·
            refine ⟨4334324030932219622849393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2889549353954813081899595 4334324030932219622849393)
            ·
              refine ⟨3250743023199164717137045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4334324030932219622849393 3250743023199164717137045)
              ·
                refine ⟨152378579212460846115799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3250743023199164717137045 152378579212460846115799)
                ·
                  rfl

theorem cell22_4006209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 6].length) (baseStart_4006209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006209 prefixEnd_4006209 := by exact prefixLift 4006209
  have htrace : WordTrace (prefixWord ++ tailWord_4006209) baseStart_4006209 baseEnd_4006209 := by
    simpa [prefixWord, tailWord_4006209, baseEnd_4006209] using wordTrace_append hprefix tailTrace_4006209
  have hstable : (prefixWord ++ tailWord_4006209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006209).length < 2 ^ (prefixWord ++ tailWord_4006209).sum := by decide
  have hdescent : baseEnd_4006209 < baseStart_4006209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006224 : List Nat := [2, 1, 1, 1, 1, 8, 1, 3, 1, 3]
def baseStart_4006224 : Nat := 118140960795 + 4006224 * 2 ^ 59
def prefixEnd_4006224 : Nat := 4983230072969 + 3 ^ 40 * 4006224 * 2
def baseEnd_4006224 : Nat := 1371412347718692575917145

theorem tailTrace_4006224 : CollatzResearch.WordTrace tailWord_4006224 prefixEnd_4006224 1371412347718692575917145 := by
  unfold tailWord_4006224
  simp only [CollatzResearch.WordTrace]
  refine ⟨73059496719071065715840863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97412662292094754287787817 73059496719071065715840863)
  ·
    refine ⟨109589245078606598573761295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73059496719071065715840863 109589245078606598573761295)
    ·
      refine ⟨164383867617909897860641943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109589245078606598573761295 164383867617909897860641943)
      ·
        refine ⟨246575801426864846790962915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164383867617909897860641943 246575801426864846790962915)
        ·
          refine ⟨369863702140297270186444373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246575801426864846790962915 369863702140297270186444373)
          ·
            refine ⟨4334340259456608634997395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 369863702140297270186444373 4334340259456608634997395)
            ·
              refine ⟨6501510389184912952496093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4334340259456608634997395 6501510389184912952496093)
              ·
                refine ⟨2438066395944342357186035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6501510389184912952496093 2438066395944342357186035)
                ·
                  refine ⟨3657099593916513535779053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438066395944342357186035 3657099593916513535779053)
                  ·
                    refine ⟨1371412347718692575917145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3657099593916513535779053 1371412347718692575917145)
                    ·
                      rfl

theorem cell22_4006224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 1, 3].length) (baseStart_4006224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006224 prefixEnd_4006224 := by exact prefixLift 4006224
  have htrace : WordTrace (prefixWord ++ tailWord_4006224) baseStart_4006224 baseEnd_4006224 := by
    simpa [prefixWord, tailWord_4006224, baseEnd_4006224] using wordTrace_append hprefix tailTrace_4006224
  have hstable : (prefixWord ++ tailWord_4006224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006224).length < 2 ^ (prefixWord ++ tailWord_4006224).sum := by decide
  have hdescent : baseEnd_4006224 < baseStart_4006224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006233 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 5, 4]
def baseStart_4006233 : Nat := 118140960795 + 4006233 * 2 ^ 59
def prefixEnd_4006233 : Nat := 4983230072969 + 3 ^ 40 * 4006233 * 2
def baseEnd_4006233 : Nat := 1371415428602619552442117

theorem tailTrace_4006233 : CollatzResearch.WordTrace tailWord_4006233 prefixEnd_4006233 1371415428602619552442117 := by
  unfold tailWord_4006233
  simp only [CollatzResearch.WordTrace]
  refine ⟨146119321695109525968759353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97412881130073017312506235 146119321695109525968759353)
  ·
    refine ⟨109589491271332144476569515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146119321695109525968759353 109589491271332144476569515)
    ·
      refine ⟨164384236906998216714854273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109589491271332144476569515 164384236906998216714854273)
      ·
        refine ⟨123288177680248662536140705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164384236906998216714854273 123288177680248662536140705)
        ·
          refine ⟨92466133260186496902105529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123288177680248662536140705 92466133260186496902105529)
          ·
            refine ⟨69349599945139872676579147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92466133260186496902105529 69349599945139872676579147)
            ·
              refine ⟨104024399917709809014868721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69349599945139872676579147 104024399917709809014868721)
              ·
                refine ⟨78018299938282356761151541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104024399917709809014868721 78018299938282356761151541)
                ·
                  refine ⟨7314215619213970946357957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78018299938282356761151541 7314215619213970946357957)
                  ·
                    refine ⟨1371415428602619552442117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7314215619213970946357957 1371415428602619552442117)
                    ·
                      rfl

theorem cell22_4006233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_4006233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006233 prefixEnd_4006233 := by exact prefixLift 4006233
  have htrace : WordTrace (prefixWord ++ tailWord_4006233) baseStart_4006233 baseEnd_4006233 := by
    simpa [prefixWord, tailWord_4006233, baseEnd_4006233] using wordTrace_append hprefix tailTrace_4006233
  have hstable : (prefixWord ++ tailWord_4006233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006233).length < 2 ^ (prefixWord ++ tailWord_4006233).sum := by decide
  have hdescent : baseEnd_4006233 < baseStart_4006233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006267 : List Nat := [1, 1, 1, 1, 1, 9, 1, 2, 1, 4]
def baseStart_4006267 : Nat := 118140960795 + 4006267 * 2 ^ 59
def prefixEnd_4006267 : Nat := 4983230072969 + 3 ^ 40 * 4006267 * 2
def baseEnd_4006267 : Nat := 1371427067497454797092013

theorem tailTrace_4006267 : CollatzResearch.WordTrace tailWord_4006267 prefixEnd_4006267 1371427067497454797092013 := by
  unfold tailWord_4006267
  simp only [CollatzResearch.WordTrace]
  refine ⟨146120561776986349775497055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97413707851324233183664703 146120561776986349775497055)
  ·
    refine ⟨219180842665479524663245583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146120561776986349775497055 219180842665479524663245583)
    ·
      refine ⟨328771263998219286994868375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219180842665479524663245583 328771263998219286994868375)
      ·
        refine ⟨493156895997328930492302563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328771263998219286994868375 493156895997328930492302563)
        ·
          refine ⟨739735343995993395738453845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493156895997328930492302563 739735343995993395738453845)
          ·
            refine ⟨4334386781226523803155003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 739735343995993395738453845 4334386781226523803155003)
            ·
              refine ⟨6501580171839785704732505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4334386781226523803155003 6501580171839785704732505)
              ·
                refine ⟨4876185128879839278549379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6501580171839785704732505 4876185128879839278549379)
                ·
                  refine ⟨7314277693319758917824069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4876185128879839278549379 7314277693319758917824069)
                  ·
                    refine ⟨1371427067497454797092013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7314277693319758917824069 1371427067497454797092013)
                    ·
                      rfl

theorem cell22_4006267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 4].length) (baseStart_4006267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006267 prefixEnd_4006267 := by exact prefixLift 4006267
  have htrace : WordTrace (prefixWord ++ tailWord_4006267) baseStart_4006267 baseEnd_4006267 := by
    simpa [prefixWord, tailWord_4006267, baseEnd_4006267] using wordTrace_append hprefix tailTrace_4006267
  have hstable : (prefixWord ++ tailWord_4006267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006267).length < 2 ^ (prefixWord ++ tailWord_4006267).sum := by decide
  have hdescent : baseEnd_4006267 < baseStart_4006267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006280 : List Nat := [2, 1, 3, 3, 1, 1, 3, 2, 1, 5]
def baseStart_4006280 : Nat := 118140960795 + 4006280 * 2 ^ 59
def prefixEnd_4006280 : Nat := 4983230072969 + 3 ^ 40 * 4006280 * 2
def baseEnd_4006280 : Nat := 1371431517663127096516973

theorem tailTrace_4006280 : CollatzResearch.WordTrace tailWord_4006280 prefixEnd_4006280 1371431517663127096516973 := by
  unfold tailWord_4006280
  simp only [CollatzResearch.WordTrace]
  refine ⟨73060517962969626497860147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97414023950626168663813529 73060517962969626497860147)
  ·
    refine ⟨109590776944454439746790221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73060517962969626497860147 109590776944454439746790221)
    ·
      refine ⟨41096541354170414905046333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109590776944454439746790221 41096541354170414905046333)
      ·
        refine ⟨15411203007813905589392375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41096541354170414905046333 15411203007813905589392375)
        ·
          refine ⟨23116804511720858384088563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15411203007813905589392375 23116804511720858384088563)
          ·
            refine ⟨34675206767581287576132845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23116804511720858384088563 34675206767581287576132845)
            ·
              refine ⟨13003202537842982841049817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34675206767581287576132845 13003202537842982841049817)
              ·
                refine ⟨9752401903382237130787363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13003202537842982841049817 9752401903382237130787363)
                ·
                  refine ⟨14628602855073355696181045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9752401903382237130787363 14628602855073355696181045)
                  ·
                    refine ⟨1371431517663127096516973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14628602855073355696181045 1371431517663127096516973)
                    ·
                      rfl

theorem cell22_4006280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_4006280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006280 prefixEnd_4006280 := by exact prefixLift 4006280
  have htrace : WordTrace (prefixWord ++ tailWord_4006280) baseStart_4006280 baseEnd_4006280 := by
    simpa [prefixWord, tailWord_4006280, baseEnd_4006280] using wordTrace_append hprefix tailTrace_4006280
  have hstable : (prefixWord ++ tailWord_4006280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006280).length < 2 ^ (prefixWord ++ tailWord_4006280).sum := by decide
  have hdescent : baseEnd_4006280 < baseStart_4006280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006295 : List Nat := [1, 1, 3, 3, 1, 1, 4, 2, 2, 4]
def baseStart_4006295 : Nat := 118140960795 + 4006295 * 2 ^ 59
def prefixEnd_4006295 : Nat := 4983230072969 + 3 ^ 40 * 4006295 * 2
def baseEnd_4006295 : Nat := 1371436652469672057391927

theorem tailTrace_4006295 : CollatzResearch.WordTrace tailWord_4006295 prefixEnd_4006295 1371436652469672057391927 := by
  unfold tailWord_4006295
  simp only [CollatzResearch.WordTrace]
  refine ⟨146121583020884910557516339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97414388680589940371677559 146121583020884910557516339)
  ·
    refine ⟨219182374531327365836274509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146121583020884910557516339 219182374531327365836274509)
    ·
      refine ⟨82193390449247762188602941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219182374531327365836274509 82193390449247762188602941)
      ·
        refine ⟨30822521418467910820726103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82193390449247762188602941 30822521418467910820726103)
        ·
          refine ⟨46233782127701866231089155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30822521418467910820726103 46233782127701866231089155)
          ·
            refine ⟨69350673191552799346633733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46233782127701866231089155 69350673191552799346633733)
            ·
              refine ⟨13003251223416149877493825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69350673191552799346633733 13003251223416149877493825)
              ·
                refine ⟨9752438417562112408120369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13003251223416149877493825 9752438417562112408120369)
                ·
                  refine ⟨7314328813171584306090277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9752438417562112408120369 7314328813171584306090277)
                  ·
                    refine ⟨1371436652469672057391927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7314328813171584306090277 1371436652469672057391927)
                    ·
                      rfl

theorem cell22_4006295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_4006295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006295 prefixEnd_4006295 := by exact prefixLift 4006295
  have htrace : WordTrace (prefixWord ++ tailWord_4006295) baseStart_4006295 baseEnd_4006295 := by
    simpa [prefixWord, tailWord_4006295, baseEnd_4006295] using wordTrace_append hprefix tailTrace_4006295
  have hstable : (prefixWord ++ tailWord_4006295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006295).length < 2 ^ (prefixWord ++ tailWord_4006295).sum := by decide
  have hdescent : baseEnd_4006295 < baseStart_4006295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006297 : List Nat := [1, 2, 1, 2, 1, 4, 4, 2, 2, 3]
def baseStart_4006297 : Nat := 118140960795 + 4006297 * 2 ^ 59
def prefixEnd_4006297 : Nat := 4983230072969 + 3 ^ 40 * 4006297 * 2
def baseEnd_4006297 : Nat := 1371437337110544718841921

theorem tailTrace_4006297 : CollatzResearch.WordTrace tailWord_4006297 prefixEnd_4006297 1371437337110544718841921 := by
  unfold tailWord_4006297
  simp only [CollatzResearch.WordTrace]
  refine ⟨146121655966877664899089145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97414437311251776599392763 146121655966877664899089145)
  ·
    refine ⟨109591241975158248674316859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146121655966877664899089145 109591241975158248674316859)
    ·
      refine ⟨164386862962737373011475289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109591241975158248674316859 164386862962737373011475289)
      ·
        refine ⟨123290147222053029758606467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164386862962737373011475289 123290147222053029758606467)
        ·
          refine ⟨184935220833079544637909701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123290147222053029758606467 184935220833079544637909701)
          ·
            refine ⟨34675353906202414619608069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184935220833079544637909701 34675353906202414619608069)
            ·
              refine ⟨6501628857412952741176513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34675353906202414619608069 6501628857412952741176513)
              ·
                refine ⟨4876221643059714555882385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6501628857412952741176513 4876221643059714555882385)
                ·
                  refine ⟨3657166232294785916911789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4876221643059714555882385 3657166232294785916911789)
                  ·
                    refine ⟨1371437337110544718841921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3657166232294785916911789 1371437337110544718841921)
                    ·
                      rfl

theorem cell22_4006297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 3].length) (baseStart_4006297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006297 prefixEnd_4006297 := by exact prefixLift 4006297
  have htrace : WordTrace (prefixWord ++ tailWord_4006297) baseStart_4006297 baseEnd_4006297 := by
    simpa [prefixWord, tailWord_4006297, baseEnd_4006297] using wordTrace_append hprefix tailTrace_4006297
  have hstable : (prefixWord ++ tailWord_4006297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006297).length < 2 ^ (prefixWord ++ tailWord_4006297).sum := by decide
  have hdescent : baseEnd_4006297 < baseStart_4006297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006406 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_4006406 : Nat := 118140960795 + 4006406 * 2 ^ 59
def prefixEnd_4006406 : Nat := 4983230072969 + 3 ^ 40 * 4006406 * 2
def baseEnd_4006406 : Nat := 457158216679368255955529

theorem tailTrace_4006406 : CollatzResearch.WordTrace tailWord_4006406 prefixEnd_4006406 457158216679368255955529 := by
  unfold tailWord_4006406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4566425985108836766087721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97417087682321851009871381 4566425985108836766087721)
  ·
    refine ⟨3424819488831627574565791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4566425985108836766087721 3424819488831627574565791)
    ·
      refine ⟨5137229233247441361848687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3424819488831627574565791 5137229233247441361848687)
      ·
        refine ⟨7705843849871162042773031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5137229233247441361848687 7705843849871162042773031)
        ·
          refine ⟨11558765774806743064159547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7705843849871162042773031 11558765774806743064159547)
          ·
            refine ⟨17338148662210114596239321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11558765774806743064159547 17338148662210114596239321)
            ·
              refine ⟨13003611496657585947179491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17338148662210114596239321 13003611496657585947179491)
              ·
                refine ⟨19505417244986378920769237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13003611496657585947179491 19505417244986378920769237)
                ·
                  refine ⟨457158216679368255955529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19505417244986378920769237 457158216679368255955529)
                  ·
                    rfl

theorem cell22_4006406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_4006406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006406 prefixEnd_4006406 := by exact prefixLift 4006406
  have htrace : WordTrace (prefixWord ++ tailWord_4006406) baseStart_4006406 baseEnd_4006406 := by
    simpa [prefixWord, tailWord_4006406, baseEnd_4006406] using wordTrace_append hprefix tailTrace_4006406
  have hstable : (prefixWord ++ tailWord_4006406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006406).length < 2 ^ (prefixWord ++ tailWord_4006406).sum := by decide
  have hdescent : baseEnd_4006406 < baseStart_4006406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006423 : List Nat := [1, 1, 3, 6, 2, 1, 2, 1, 5]
def baseStart_4006423 : Nat := 118140960795 + 4006423 * 2 ^ 59
def prefixEnd_4006423 : Nat := 4983230072969 + 3 ^ 40 * 4006423 * 2
def baseEnd_4006423 : Nat := 457160156495174130063845

theorem tailTrace_4006423 : CollatzResearch.WordTrace tailWord_4006423 prefixEnd_4006423 457160156495174130063845 := by
  unfold tailWord_4006423
  simp only [CollatzResearch.WordTrace]
  refine ⟨146126251564421188418175923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97417501042947458945450615 146126251564421188418175923)
  ·
    refine ⟨219189377346631782627263885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146126251564421188418175923 219189377346631782627263885)
    ·
      refine ⟨82196016504986918485223957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219189377346631782627263885 82196016504986918485223957)
      ·
        refine ⟨3852938273671261803994873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82196016504986918485223957 3852938273671261803994873)
        ·
          refine ⟨2889703705253446352996155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3852938273671261803994873 2889703705253446352996155)
          ·
            refine ⟨4334555557880169529494233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2889703705253446352996155 4334555557880169529494233)
            ·
              refine ⟨3250916668410127147120675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4334555557880169529494233 3250916668410127147120675)
              ·
                refine ⟨4876375002615190720681013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3250916668410127147120675 4876375002615190720681013)
                ·
                  refine ⟨457160156495174130063845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4876375002615190720681013 457160156495174130063845)
                  ·
                    rfl

theorem cell22_4006423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 5].length) (baseStart_4006423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006423 prefixEnd_4006423 := by exact prefixLift 4006423
  have htrace : WordTrace (prefixWord ++ tailWord_4006423) baseStart_4006423 baseEnd_4006423 := by
    simpa [prefixWord, tailWord_4006423, baseEnd_4006423] using wordTrace_append hprefix tailTrace_4006423
  have hstable : (prefixWord ++ tailWord_4006423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006423).length < 2 ^ (prefixWord ++ tailWord_4006423).sum := by decide
  have hdescent : baseEnd_4006423 < baseStart_4006423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006462 : List Nat := [4, 2, 1, 4, 11]
def baseStart_4006462 : Nat := 118140960795 + 4006462 * 2 ^ 59
def prefixEnd_4006462 : Nat := 4983230072969 + 3 ^ 40 * 4006462 * 2
def baseEnd_4006462 : Nat := 5644007489640079376405

theorem tailTrace_4006462 : CollatzResearch.WordTrace tailWord_4006462 prefixEnd_4006462 5644007489640079376405 := by
  unfold tailWord_4006462
  simp only [CollatzResearch.WordTrace]
  refine ⟨18265959251409987259855705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97418449340853265385897093 18265959251409987259855705)
  ·
    refine ⟨13699469438557490444891779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18265959251409987259855705 13699469438557490444891779)
    ·
      refine ⟨20549204157836235667337669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13699469438557490444891779 20549204157836235667337669)
      ·
        refine ⟨3852975779594294187625813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20549204157836235667337669 3852975779594294187625813)
        ·
          refine ⟨5644007489640079376405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3852975779594294187625813 5644007489640079376405)
          ·
            rfl

theorem cell22_4006462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 11].length) (baseStart_4006462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006462 prefixEnd_4006462 := by exact prefixLift 4006462
  have htrace : WordTrace (prefixWord ++ tailWord_4006462) baseStart_4006462 baseEnd_4006462 := by
    simpa [prefixWord, tailWord_4006462, baseEnd_4006462] using wordTrace_append hprefix tailTrace_4006462
  have hstable : (prefixWord ++ tailWord_4006462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006462).length < 2 ^ (prefixWord ++ tailWord_4006462).sum := by decide
  have hdescent : baseEnd_4006462 < baseStart_4006462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006475 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 2, 6]
def baseStart_4006475 : Nat := 118140960795 + 4006475 * 2 ^ 59
def prefixEnd_4006475 : Nat := 4983230072969 + 3 ^ 40 * 4006475 * 2
def baseEnd_4006475 : Nat := 1371498270148211587891375

theorem tailTrace_4006475 : CollatzResearch.WordTrace tailWord_4006475 prefixEnd_4006475 1371498270148211587891375 := by
  unfold tailWord_4006475
  simp only [CollatzResearch.WordTrace]
  refine ⟨146128148160232801299068879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97418765440155200866045919 146128148160232801299068879)
  ·
    refine ⟨219192222240349201948603319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146128148160232801299068879 219192222240349201948603319)
    ·
      refine ⟨328788333360523802922904979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219192222240349201948603319 328788333360523802922904979)
      ·
        refine ⟨493182500040785704384357469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328788333360523802922904979 493182500040785704384357469)
        ·
          refine ⟨184943437515294639144134051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493182500040785704384357469 184943437515294639144134051)
          ·
            refine ⟨277415156272941958716201077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184943437515294639144134051 277415156272941958716201077)
            ·
              refine ⟨26007670900588308629643851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277415156272941958716201077 26007670900588308629643851)
              ·
                refine ⟨39011506350882462944465777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26007670900588308629643851 39011506350882462944465777)
                ·
                  refine ⟨29258629763161847208349333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39011506350882462944465777 29258629763161847208349333)
                  ·
                    refine ⟨1371498270148211587891375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29258629763161847208349333 1371498270148211587891375)
                    ·
                      rfl

theorem cell22_4006475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 6].length) (baseStart_4006475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006475 prefixEnd_4006475 := by exact prefixLift 4006475
  have htrace : WordTrace (prefixWord ++ tailWord_4006475) baseStart_4006475 baseEnd_4006475 := by
    simpa [prefixWord, tailWord_4006475, baseEnd_4006475] using wordTrace_append hprefix tailTrace_4006475
  have hstable : (prefixWord ++ tailWord_4006475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006475).length < 2 ^ (prefixWord ++ tailWord_4006475).sum := by decide
  have hdescent : baseEnd_4006475 < baseStart_4006475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006490 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 11]
def baseStart_4006490 : Nat := 118140960795 + 4006490 * 2 ^ 59
def prefixEnd_4006490 : Nat := 4983230072969 + 3 ^ 40 * 4006490 * 2
def baseEnd_4006490 : Nat := 457167801651585516255443

theorem tailTrace_4006490 : CollatzResearch.WordTrace tailWord_4006490 prefixEnd_4006490 457167801651585516255443 := by
  unfold tailWord_4006490
  simp only [CollatzResearch.WordTrace]
  refine ⟨36532173813794614715216231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97419130170118972573909949 36532173813794614715216231)
  ·
    refine ⟨54798260720691922072824347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36532173813794614715216231 54798260720691922072824347)
    ·
      refine ⟨82197391081037883109236521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54798260720691922072824347 82197391081037883109236521)
      ·
        refine ⟨61648043310778412331927391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82197391081037883109236521 61648043310778412331927391)
        ·
          refine ⟨92472064966167618497891087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61648043310778412331927391 92472064966167618497891087)
          ·
            refine ⟨138708097449251427746836631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92472064966167618497891087 138708097449251427746836631)
            ·
              refine ⟨208062146173877141620254947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138708097449251427746836631 208062146173877141620254947)
              ·
                refine ⟨312093219260815712430382421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208062146173877141620254947 312093219260815712430382421)
                ·
                  refine ⟨457167801651585516255443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 312093219260815712430382421 457167801651585516255443)
                  ·
                    rfl

theorem cell22_4006490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_4006490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006490 prefixEnd_4006490 := by exact prefixLift 4006490
  have htrace : WordTrace (prefixWord ++ tailWord_4006490) baseStart_4006490 baseEnd_4006490 := by
    simpa [prefixWord, tailWord_4006490, baseEnd_4006490] using wordTrace_append hprefix tailTrace_4006490
  have hstable : (prefixWord ++ tailWord_4006490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006490).length < 2 ^ (prefixWord ++ tailWord_4006490).sum := by decide
  have hdescent : baseEnd_4006490 < baseStart_4006490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006498 : List Nat := [3, 3, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_4006498 : Nat := 118140960795 + 4006498 * 2 ^ 59
def prefixEnd_4006498 : Nat := 4983230072969 + 3 ^ 40 * 4006498 * 2
def baseEnd_4006498 : Nat := 1371506143518247194566305

theorem tailTrace_4006498 : CollatzResearch.WordTrace tailWord_4006498 prefixEnd_4006498 1371506143518247194566305 := by
  unfold tailWord_4006498
  simp only [CollatzResearch.WordTrace]
  refine ⟨36532246759787369056789037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97419324692766317484770765 36532246759787369056789037)
  ·
    refine ⟨13699592534920263396295889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36532246759787369056789037 13699592534920263396295889)
    ·
      refine ⟨10274694401190197547221917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13699592534920263396295889 10274694401190197547221917)
      ·
        refine ⟨3853010400446324080208219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10274694401190197547221917 3853010400446324080208219)
        ·
          refine ⟨5779515600669486120312329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3853010400446324080208219 5779515600669486120312329)
          ·
            refine ⟨4334636700502114590234247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5779515600669486120312329 4334636700502114590234247)
            ·
              refine ⟨6501955050753171885351371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4334636700502114590234247 6501955050753171885351371)
              ·
                refine ⟨9752932576129757828027057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6501955050753171885351371 9752932576129757828027057)
                ·
                  refine ⟨7314699432097318371020293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9752932576129757828027057 7314699432097318371020293)
                  ·
                    refine ⟨1371506143518247194566305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7314699432097318371020293 1371506143518247194566305)
                    ·
                      rfl

theorem cell22_4006498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_4006498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006498 prefixEnd_4006498 := by exact prefixLift 4006498
  have htrace : WordTrace (prefixWord ++ tailWord_4006498) baseStart_4006498 baseEnd_4006498 := by
    simpa [prefixWord, tailWord_4006498, baseEnd_4006498] using wordTrace_append hprefix tailTrace_4006498
  have hstable : (prefixWord ++ tailWord_4006498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006498).length < 2 ^ (prefixWord ++ tailWord_4006498).sum := by decide
  have hdescent : baseEnd_4006498 < baseStart_4006498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006505 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 3, 7]
def baseStart_4006505 : Nat := 118140960795 + 4006505 * 2 ^ 59
def prefixEnd_4006505 : Nat := 4983230072969 + 3 ^ 40 * 4006505 * 2
def baseEnd_4006505 : Nat := 1371508539761301509641283

theorem tailTrace_4006505 : CollatzResearch.WordTrace tailWord_4006505 prefixEnd_4006505 1371508539761301509641283 := by
  unfold tailWord_4006505
  simp only [CollatzResearch.WordTrace]
  refine ⟨146129242350124116422660969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97419494900082744281773979 146129242350124116422660969)
  ·
    refine ⟨109596931762593087316995727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146129242350124116422660969 109596931762593087316995727)
    ·
      refine ⟨164395397643889630975493591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109596931762593087316995727 164395397643889630975493591)
      ·
        refine ⟨246593096465834446463240387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164395397643889630975493591 246593096465834446463240387)
        ·
          refine ⟨369889644698751669694860581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246593096465834446463240387 369889644698751669694860581)
          ·
            refine ⟨69354308381015938067786359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 369889644698751669694860581 69354308381015938067786359)
            ·
              refine ⟨104031462571523907101679539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69354308381015938067786359 104031462571523907101679539)
              ·
                refine ⟨156047193857285860652519309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104031462571523907101679539 156047193857285860652519309)
                ·
                  refine ⟨58517697696482197744694741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156047193857285860652519309 58517697696482197744694741)
                  ·
                    refine ⟨1371508539761301509641283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58517697696482197744694741 1371508539761301509641283)
                    ·
                      rfl

theorem cell22_4006505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_4006505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006505 prefixEnd_4006505 := by exact prefixLift 4006505
  have htrace : WordTrace (prefixWord ++ tailWord_4006505) baseStart_4006505 baseEnd_4006505 := by
    simpa [prefixWord, tailWord_4006505, baseEnd_4006505] using wordTrace_append hprefix tailTrace_4006505
  have hstable : (prefixWord ++ tailWord_4006505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006505).length < 2 ^ (prefixWord ++ tailWord_4006505).sum := by decide
  have hdescent : baseEnd_4006505 < baseStart_4006505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006552 : List Nat := [2, 1, 2, 4, 1, 1, 1, 4, 6]
def baseStart_4006552 : Nat := 118140960795 + 4006552 * 2 ^ 59
def prefixEnd_4006552 : Nat := 4983230072969 + 3 ^ 40 * 4006552 * 2
def baseEnd_4006552 : Nat := 457174876273936351238713

theorem tailTrace_4006552 : CollatzResearch.WordTrace tailWord_4006552 prefixEnd_4006552 457174876273936351238713 := by
  unfold tailWord_4006552
  simp only [CollatzResearch.WordTrace]
  refine ⟨73065478290476921724810955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97420637720635895633081273 73065478290476921724810955)
  ·
    refine ⟨109598217435715382587216433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73065478290476921724810955 109598217435715382587216433)
    ·
      refine ⟨82198663076786536940412325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109598217435715382587216433 82198663076786536940412325)
      ·
        refine ⟨15412249326897475676327311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82198663076786536940412325 15412249326897475676327311)
        ·
          refine ⟨23118373990346213514490967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15412249326897475676327311 23118373990346213514490967)
          ·
            refine ⟨34677560985519320271736451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23118373990346213514490967 34677560985519320271736451)
            ·
              refine ⟨52016341478278980407604677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34677560985519320271736451 52016341478278980407604677)
              ·
                refine ⟨9753064027177308826425877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52016341478278980407604677 9753064027177308826425877)
                ·
                  refine ⟨457174876273936351238713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9753064027177308826425877 457174876273936351238713)
                  ·
                    rfl

theorem cell22_4006552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 6].length) (baseStart_4006552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006552 prefixEnd_4006552 := by exact prefixLift 4006552
  have htrace : WordTrace (prefixWord ++ tailWord_4006552) baseStart_4006552 baseEnd_4006552 := by
    simpa [prefixWord, tailWord_4006552, baseEnd_4006552] using wordTrace_append hprefix tailTrace_4006552
  have hstable : (prefixWord ++ tailWord_4006552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006552).length < 2 ^ (prefixWord ++ tailWord_4006552).sum := by decide
  have hdescent : baseEnd_4006552 < baseStart_4006552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006586 : List Nat := [3, 1, 1, 1, 2, 3, 5, 2, 4]
def baseStart_4006586 : Nat := 118140960795 + 4006586 * 2 ^ 59
def prefixEnd_4006586 : Nat := 4983230072969 + 3 ^ 40 * 4006586 * 2
def baseEnd_4006586 : Nat := 457178755905548099455345

theorem tailTrace_4006586 : CollatzResearch.WordTrace tailWord_4006586 prefixEnd_4006586 457178755905548099455345 := by
  unfold tailWord_4006586
  simp only [CollatzResearch.WordTrace]
  refine ⟨36533049165707666814089903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97421464441887111504239741 36533049165707666814089903)
  ·
    refine ⟨54799573748561500221134855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36533049165707666814089903 54799573748561500221134855)
    ·
      refine ⟨82199360622842250331702283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54799573748561500221134855 82199360622842250331702283)
      ·
        refine ⟨123299040934263375497553425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82199360622842250331702283 123299040934263375497553425)
        ·
          refine ⟨92474280700697531623165069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123299040934263375497553425 92474280700697531623165069)
          ·
            refine ⟨34677855262761574358686901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92474280700697531623165069 34677855262761574358686901)
            ·
              refine ⟨3251048930883897596126897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34677855262761574358686901 3251048930883897596126897)
              ·
                refine ⟨2438286698162923197095173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3251048930883897596126897 2438286698162923197095173)
                ·
                  refine ⟨457178755905548099455345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2438286698162923197095173 457178755905548099455345)
                  ·
                    rfl

theorem cell22_4006586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_4006586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006586 prefixEnd_4006586 := by exact prefixLift 4006586
  have htrace : WordTrace (prefixWord ++ tailWord_4006586) baseStart_4006586 baseEnd_4006586 := by
    simpa [prefixWord, tailWord_4006586, baseEnd_4006586] using wordTrace_append hprefix tailTrace_4006586
  have hstable : (prefixWord ++ tailWord_4006586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006586).length < 2 ^ (prefixWord ++ tailWord_4006586).sum := by decide
  have hdescent : baseEnd_4006586 < baseStart_4006586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006605 : List Nat := [1, 6, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_4006605 : Nat := 118140960795 + 4006605 * 2 ^ 59
def prefixEnd_4006605 : Nat := 4983230072969 + 3 ^ 40 * 4006605 * 2
def baseEnd_4006605 : Nat := 1371542771804934582140977

theorem tailTrace_4006605 : CollatzResearch.WordTrace tailWord_4006605 prefixEnd_4006605 1371542771804934582140977 := by
  unfold tailWord_4006605
  simp only [CollatzResearch.WordTrace]
  refine ⟨146132889649761833501301269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97421926433174555667534179 146132889649761833501301269)
  ·
    refine ⟨6849979202332585945373497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146132889649761833501301269 6849979202332585945373497)
    ·
      refine ⟨5137484401749439459030123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6849979202332585945373497 5137484401749439459030123)
      ·
        refine ⟨7706226602624159188545185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5137484401749439459030123 7706226602624159188545185)
        ·
          refine ⟨5779669951968119391408889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7706226602624159188545185 5779669951968119391408889)
          ·
            refine ⟨4334752463976089543556667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5779669951968119391408889 4334752463976089543556667)
            ·
              refine ⟨6502128695964134315335001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4334752463976089543556667 6502128695964134315335001)
              ·
                refine ⟨4876596521973100736501251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6502128695964134315335001 4876596521973100736501251)
                ·
                  refine ⟨7314894782959651104751877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4876596521973100736501251 7314894782959651104751877)
                  ·
                    refine ⟨1371542771804934582140977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7314894782959651104751877 1371542771804934582140977)
                    ·
                      rfl

theorem cell22_4006605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_4006605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006605 prefixEnd_4006605 := by exact prefixLift 4006605
  have htrace : WordTrace (prefixWord ++ tailWord_4006605) baseStart_4006605 baseEnd_4006605 := by
    simpa [prefixWord, tailWord_4006605, baseEnd_4006605] using wordTrace_append hprefix tailTrace_4006605
  have hstable : (prefixWord ++ tailWord_4006605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006605).length < 2 ^ (prefixWord ++ tailWord_4006605).sum := by decide
  have hdescent : baseEnd_4006605 < baseStart_4006605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006646 : List Nat := [5, 1, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_4006646 : Nat := 118140960795 + 4006646 * 2 ^ 59
def prefixEnd_4006646 : Nat := 4983230072969 + 3 ^ 40 * 4006646 * 2
def baseEnd_4006646 : Nat := 1371556806942824141865851

theorem tailTrace_4006646 : CollatzResearch.WordTrace tailWord_4006646 prefixEnd_4006646 1371556806942824141865851 := by
  unfold tailWord_4006646
  simp only [CollatzResearch.WordTrace]
  refine ⟨9133399065163331093971487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97422923361742198335695861 9133399065163331093971487)
  ·
    refine ⟨13700098597744996640957231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9133399065163331093971487 13700098597744996640957231)
    ·
      refine ⟨20550147896617494961435847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13700098597744996640957231 20550147896617494961435847)
      ·
        refine ⟨30825221844926242442153771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20550147896617494961435847 30825221844926242442153771)
        ·
          refine ⟨46237832767389363663230657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30825221844926242442153771 46237832767389363663230657)
          ·
            refine ⟨34678374575542022747422993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46237832767389363663230657 34678374575542022747422993)
            ·
              refine ⟨26008780931656517060567245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34678374575542022747422993 26008780931656517060567245)
              ·
                refine ⟨9753292849371193897712717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26008780931656517060567245 9753292849371193897712717)
                ·
                  refine ⟨3657484818514197711642269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9753292849371193897712717 3657484818514197711642269)
                  ·
                    refine ⟨1371556806942824141865851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3657484818514197711642269 1371556806942824141865851)
                    ·
                      rfl

theorem cell22_4006646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_4006646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006646 prefixEnd_4006646 := by exact prefixLift 4006646
  have htrace : WordTrace (prefixWord ++ tailWord_4006646) baseStart_4006646 baseEnd_4006646 := by
    simpa [prefixWord, tailWord_4006646, baseEnd_4006646] using wordTrace_append hprefix tailTrace_4006646
  have hstable : (prefixWord ++ tailWord_4006646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006646).length < 2 ^ (prefixWord ++ tailWord_4006646).sum := by decide
  have hdescent : baseEnd_4006646 < baseStart_4006646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006710 : List Nat := [5, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_4006710 : Nat := 118140960795 + 4006710 * 2 ^ 59
def prefixEnd_4006710 : Nat := 4983230072969 + 3 ^ 40 * 4006710 * 2
def baseEnd_4006710 : Nat := 457192905150249769421885

theorem tailTrace_4006710 : CollatzResearch.WordTrace tailWord_4006710 prefixEnd_4006710 457192905150249769421885 := by
  unfold tailWord_4006710
  simp only [CollatzResearch.WordTrace]
  refine ⟨9133544957148839777117099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97424479542920957622582389 9133544957148839777117099)
  ·
    refine ⟨13700317435723259665675649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9133544957148839777117099 13700317435723259665675649)
    ·
      refine ⟨10275238076792444749256737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13700317435723259665675649 10275238076792444749256737)
      ·
        refine ⟨7706428557594333561942553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10275238076792444749256737 7706428557594333561942553)
        ·
          refine ⟨5779821418195750171456915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7706428557594333561942553 5779821418195750171456915)
          ·
            refine ⟨8669732127293625257185373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5779821418195750171456915 8669732127293625257185373)
            ·
              refine ⟨3251149547735109471444515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8669732127293625257185373 3251149547735109471444515)
              ·
                refine ⟨4876724321602664207166773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3251149547735109471444515 4876724321602664207166773)
                ·
                  refine ⟨457192905150249769421885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4876724321602664207166773 457192905150249769421885)
                  ·
                    rfl

theorem cell22_4006710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_4006710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006710 prefixEnd_4006710 := by exact prefixLift 4006710
  have htrace : WordTrace (prefixWord ++ tailWord_4006710) baseStart_4006710 baseEnd_4006710 := by
    simpa [prefixWord, tailWord_4006710, baseEnd_4006710] using wordTrace_append hprefix tailTrace_4006710
  have hstable : (prefixWord ++ tailWord_4006710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006710).length < 2 ^ (prefixWord ++ tailWord_4006710).sum := by decide
  have hdescent : baseEnd_4006710 < baseStart_4006710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006734 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_4006734 : Nat := 118140960795 + 4006734 * 2 ^ 59
def prefixEnd_4006734 : Nat := 4983230072969 + 3 ^ 40 * 4006734 * 2
def baseEnd_4006734 : Nat := 1371586931141221245665581

theorem tailTrace_4006734 : CollatzResearch.WordTrace tailWord_4006734 prefixEnd_4006734 1371586931141221245665581 := by
  unfold tailWord_4006734
  simp only [CollatzResearch.WordTrace]
  refine ⟨18267199333286811066593407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97425063110862992355164837 18267199333286811066593407)
  ·
    refine ⟨27400798999930216599890111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18267199333286811066593407 27400798999930216599890111)
    ·
      refine ⟨41101198499895324899835167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27400798999930216599890111 41101198499895324899835167)
      ·
        refine ⟨61651797749842987349752751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41101198499895324899835167 61651797749842987349752751)
        ·
          refine ⟨92477696624764481024629127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61651797749842987349752751 92477696624764481024629127)
          ·
            refine ⟨138716544937146721536943691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92477696624764481024629127 138716544937146721536943691)
            ·
              refine ⟨208074817405720082305415537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138716544937146721536943691 208074817405720082305415537)
              ·
                refine ⟨156056113054290061729061653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208074817405720082305415537 156056113054290061729061653)
                ·
                  refine ⟨7315130299419846643549765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156056113054290061729061653 7315130299419846643549765)
                  ·
                    refine ⟨1371586931141221245665581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7315130299419846643549765 1371586931141221245665581)
                    ·
                      rfl

theorem cell22_4006734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_4006734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006734 prefixEnd_4006734 := by exact prefixLift 4006734
  have htrace : WordTrace (prefixWord ++ tailWord_4006734) baseStart_4006734 baseEnd_4006734 := by
    simpa [prefixWord, tailWord_4006734, baseEnd_4006734] using wordTrace_append hprefix tailTrace_4006734
  have hstable : (prefixWord ++ tailWord_4006734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006734).length < 2 ^ (prefixWord ++ tailWord_4006734).sum := by decide
  have hdescent : baseEnd_4006734 < baseStart_4006734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006781 : List Nat := [1, 4, 1, 1, 2, 1, 2, 4, 3, 3]
def baseStart_4006781 : Nat := 118140960795 + 4006781 * 2 ^ 59
def prefixEnd_4006781 : Nat := 4983230072969 + 3 ^ 40 * 4006781 * 2
def baseEnd_4006781 : Nat := 1371603020201728789740437

theorem tailTrace_4006781 : CollatzResearch.WordTrace tailWord_4006781 prefixEnd_4006781 1371603020201728789740437 := by
  unfold tailWord_4006781
  simp only [CollatzResearch.WordTrace]
  refine ⟨146139308897124215559708197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97426205931416143706472131 146139308897124215559708197)
  ·
    refine ⟨27401120418210790417445287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146139308897124215559708197 27401120418210790417445287)
    ·
      refine ⟨41101680627316185626167931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27401120418210790417445287 41101680627316185626167931)
      ·
        refine ⟨61652520940974278439251897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41101680627316185626167931 61652520940974278439251897)
        ·
          refine ⟨46239390705730708829438923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61652520940974278439251897 46239390705730708829438923)
          ·
            refine ⟨69359086058596063244158385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46239390705730708829438923 69359086058596063244158385)
            ·
              refine ⟨52019314543947047433118789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69359086058596063244158385 52019314543947047433118789)
              ·
                refine ⟨9753621476990071393709773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52019314543947047433118789 9753621476990071393709773)
                ·
                  refine ⟨3657608053871276772641165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9753621476990071393709773 3657608053871276772641165)
                  ·
                    refine ⟨1371603020201728789740437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3657608053871276772641165 1371603020201728789740437)
                    ·
                      rfl

theorem cell22_4006781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_4006781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006781 prefixEnd_4006781 := by exact prefixLift 4006781
  have htrace : WordTrace (prefixWord ++ tailWord_4006781) baseStart_4006781 baseEnd_4006781 := by
    simpa [prefixWord, tailWord_4006781, baseEnd_4006781] using wordTrace_append hprefix tailTrace_4006781
  have hstable : (prefixWord ++ tailWord_4006781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006781).length < 2 ^ (prefixWord ++ tailWord_4006781).sum := by decide
  have hdescent : baseEnd_4006781 < baseStart_4006781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006809 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 2, 5]
def baseStart_4006809 : Nat := 118140960795 + 4006809 * 2 ^ 59
def prefixEnd_4006809 : Nat := 4983230072969 + 3 ^ 40 * 4006809 * 2
def baseEnd_4006809 : Nat := 1371612605173946050040351

theorem tailTrace_4006809 : CollatzResearch.WordTrace tailWord_4006809 prefixEnd_4006809 1371612605173946050040351 := by
  unfold tailWord_4006809
  simp only [CollatzResearch.WordTrace]
  refine ⟨146140330141022776341727481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97426886760681850894484987 146140330141022776341727481)
  ·
    refine ⟨109605247605767082256295611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146140330141022776341727481 109605247605767082256295611)
    ·
      refine ⟨164407871408650623384443417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109605247605767082256295611 164407871408650623384443417)
      ·
        refine ⟨123305903556487967538332563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164407871408650623384443417 123305903556487967538332563)
        ·
          refine ⟨184958855334731951307498845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123305903556487967538332563 184958855334731951307498845)
          ·
            refine ⟨69359570750524481740312067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184958855334731951307498845 69359570750524481740312067)
            ·
              refine ⟨104039356125786722610468101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69359570750524481740312067 104039356125786722610468101)
              ·
                refine ⟨19507379273585010489462769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104039356125786722610468101 19507379273585010489462769)
                ·
                  refine ⟨14630534455188757867097077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19507379273585010489462769 14630534455188757867097077)
                  ·
                    refine ⟨1371612605173946050040351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14630534455188757867097077 1371612605173946050040351)
                    ·
                      rfl

theorem cell22_4006809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_4006809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006809 prefixEnd_4006809 := by exact prefixLift 4006809
  have htrace : WordTrace (prefixWord ++ tailWord_4006809) baseStart_4006809 baseEnd_4006809 := by
    simpa [prefixWord, tailWord_4006809, baseEnd_4006809] using wordTrace_append hprefix tailTrace_4006809
  have hstable : (prefixWord ++ tailWord_4006809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006809).length < 2 ^ (prefixWord ++ tailWord_4006809).sum := by decide
  have hdescent : baseEnd_4006809 < baseStart_4006809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006815 : List Nat := [1, 1, 2, 5, 2, 2, 1, 4, 1, 3]
def baseStart_4006815 : Nat := 118140960795 + 4006815 * 2 ^ 59
def prefixEnd_4006815 : Nat := 4983230072969 + 3 ^ 40 * 4006815 * 2
def baseEnd_4006815 : Nat := 1371614659096564034390333

theorem tailTrace_4006815 : CollatzResearch.WordTrace tailWord_4006815 prefixEnd_4006815 1371614659096564034390333 := by
  unfold tailWord_4006815
  simp only [CollatzResearch.WordTrace]
  refine ⟨146140548979001039366445899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97427032652667359577630599 146140548979001039366445899)
  ·
    refine ⟨219210823468501559049668849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146140548979001039366445899 219210823468501559049668849)
    ·
      refine ⟨164408117601376169287251637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219210823468501559049668849 164408117601376169287251637)
      ·
        refine ⟨15413261025129015870679841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164408117601376169287251637 15413261025129015870679841)
        ·
          refine ⟨11559945768846761903009881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15413261025129015870679841 11559945768846761903009881)
          ·
            refine ⟨8669959326635071427257411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11559945768846761903009881 8669959326635071427257411)
            ·
              refine ⟨13004938989952607140886117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8669959326635071427257411 13004938989952607140886117)
              ·
                refine ⟨2438426060616113838916147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13004938989952607140886117 2438426060616113838916147)
                ·
                  refine ⟨3657639090924170758374221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438426060616113838916147 3657639090924170758374221)
                  ·
                    refine ⟨1371614659096564034390333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3657639090924170758374221 1371614659096564034390333)
                    ·
                      rfl

theorem cell22_4006815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 1, 3].length) (baseStart_4006815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006815 prefixEnd_4006815 := by exact prefixLift 4006815
  have htrace : WordTrace (prefixWord ++ tailWord_4006815) baseStart_4006815 baseEnd_4006815 := by
    simpa [prefixWord, tailWord_4006815, baseEnd_4006815] using wordTrace_append hprefix tailTrace_4006815
  have hstable : (prefixWord ++ tailWord_4006815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006815).length < 2 ^ (prefixWord ++ tailWord_4006815).sum := by decide
  have hdescent : baseEnd_4006815 < baseStart_4006815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006839 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 8]
def baseStart_4006839 : Nat := 118140960795 + 4006839 * 2 ^ 59
def prefixEnd_4006839 : Nat := 4983230072969 + 3 ^ 40 * 4006839 * 2
def baseEnd_4006839 : Nat := 457207624929011990596753

theorem tailTrace_4006839 : CollatzResearch.WordTrace tailWord_4006839 prefixEnd_4006839 457207624929011990596753 := by
  unfold tailWord_4006839
  simp only [CollatzResearch.WordTrace]
  refine ⟨146141424330914091465319571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97427616220609394310213047 146141424330914091465319571)
  ·
    refine ⟨219212136496371137197979357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146141424330914091465319571 219212136496371137197979357)
    ·
      refine ⟨82204551186139176449242259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219212136496371137197979357 82204551186139176449242259)
      ·
        refine ⟨123306826779208764673863389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82204551186139176449242259 123306826779208764673863389)
        ·
          refine ⟨46240060042203286752698771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123306826779208764673863389 46240060042203286752698771)
          ·
            refine ⟨69360090063304930129048157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46240060042203286752698771 69360090063304930129048157)
            ·
              refine ⟨26010033773739348798393059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69360090063304930129048157 26010033773739348798393059)
              ·
                refine ⟨39015050660609023197589589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26010033773739348798393059 39015050660609023197589589)
                ·
                  refine ⟨457207624929011990596753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39015050660609023197589589 457207624929011990596753)
                  ·
                    rfl

theorem cell22_4006839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 8].length) (baseStart_4006839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006839 prefixEnd_4006839 := by exact prefixLift 4006839
  have htrace : WordTrace (prefixWord ++ tailWord_4006839) baseStart_4006839 baseEnd_4006839 := by
    simpa [prefixWord, tailWord_4006839, baseEnd_4006839] using wordTrace_append hprefix tailTrace_4006839
  have hstable : (prefixWord ++ tailWord_4006839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006839).length < 2 ^ (prefixWord ++ tailWord_4006839).sum := by decide
  have hdescent : baseEnd_4006839 < baseStart_4006839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006841 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 3, 4]
def baseStart_4006841 : Nat := 118140960795 + 4006841 * 2 ^ 59
def prefixEnd_4006841 : Nat := 4983230072969 + 3 ^ 40 * 4006841 * 2
def baseEnd_4006841 : Nat := 1371623559427908633240253

theorem tailTrace_4006841 : CollatzResearch.WordTrace tailWord_4006841 prefixEnd_4006841 1371623559427908633240253 := by
  unfold tailWord_4006841
  simp only [CollatzResearch.WordTrace]
  refine ⟨146141497276906845806892377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97427664851271230537928251 146141497276906845806892377)
  ·
    refine ⟨109606122957680134355169283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146141497276906845806892377 109606122957680134355169283)
    ·
      refine ⟨164409184436520201532753925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109606122957680134355169283 164409184436520201532753925)
      ·
        refine ⟨30826722081847537787391361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164409184436520201532753925 30826722081847537787391361)
        ·
          refine ⟨23120041561385653340543521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30826722081847537787391361 23120041561385653340543521)
          ·
            refine ⟨17340031171039240005407641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23120041561385653340543521 17340031171039240005407641)
            ·
              refine ⟨13005023378279430004055731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17340031171039240005407641 13005023378279430004055731)
              ·
                refine ⟨19507535067419145006083597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13005023378279430004055731 19507535067419145006083597)
                ·
                  refine ⟨7315325650282179377281349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19507535067419145006083597 7315325650282179377281349)
                  ·
                    refine ⟨1371623559427908633240253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7315325650282179377281349 1371623559427908633240253)
                    ·
                      rfl

theorem cell22_4006841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_4006841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006841 prefixEnd_4006841 := by exact prefixLift 4006841
  have htrace : WordTrace (prefixWord ++ tailWord_4006841) baseStart_4006841 baseEnd_4006841 := by
    simpa [prefixWord, tailWord_4006841, baseEnd_4006841] using wordTrace_append hprefix tailTrace_4006841
  have hstable : (prefixWord ++ tailWord_4006841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006841).length < 2 ^ (prefixWord ++ tailWord_4006841).sum := by decide
  have hdescent : baseEnd_4006841 < baseStart_4006841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006873 : List Nat := [1, 2, 1, 2, 5, 1, 2, 4, 4]
def baseStart_4006873 : Nat := 118140960795 + 4006873 * 2 ^ 59
def prefixEnd_4006873 : Nat := 4983230072969 + 3 ^ 40 * 4006873 * 2
def baseEnd_4006873 : Nat := 457211504560623738813385

theorem tailTrace_4006873 : CollatzResearch.WordTrace tailWord_4006873 prefixEnd_4006873 457211504560623738813385 := by
  unfold tailWord_4006873
  simp only [CollatzResearch.WordTrace]
  refine ⟨146142664412790915272057273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97428442941860610181371515 146142664412790915272057273)
  ·
    refine ⟨109606998309593186454042955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146142664412790915272057273 109606998309593186454042955)
    ·
      refine ⟨164410497464389779681064433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109606998309593186454042955 164410497464389779681064433)
      ·
        refine ⟨123307873098292334760798325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164410497464389779681064433 123307873098292334760798325)
        ·
          refine ⟨11560113102964906383824843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123307873098292334760798325 11560113102964906383824843)
          ·
            refine ⟨17340169654447359575737265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11560113102964906383824843 17340169654447359575737265)
            ·
              refine ⟨13005127240835519681802949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17340169654447359575737265 13005127240835519681802949)
              ·
                refine ⟨2438461357656659940338053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13005127240835519681802949 2438461357656659940338053)
                ·
                  refine ⟨457211504560623738813385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2438461357656659940338053 457211504560623738813385)
                  ·
                    rfl

theorem cell22_4006873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 4].length) (baseStart_4006873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006873 prefixEnd_4006873 := by exact prefixLift 4006873
  have htrace : WordTrace (prefixWord ++ tailWord_4006873) baseStart_4006873 baseEnd_4006873 := by
    simpa [prefixWord, tailWord_4006873, baseEnd_4006873] using wordTrace_append hprefix tailTrace_4006873
  have hstable : (prefixWord ++ tailWord_4006873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006873).length < 2 ^ (prefixWord ++ tailWord_4006873).sum := by decide
  have hdescent : baseEnd_4006873 < baseStart_4006873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006888 : List Nat := [2, 1, 4, 1, 1, 1, 2, 5, 2, 3]
def baseStart_4006888 : Nat := 118140960795 + 4006888 * 2 ^ 59
def prefixEnd_4006888 : Nat := 4983230072969 + 3 ^ 40 * 4006888 * 2
def baseEnd_4006888 : Nat := 1371639648488416177315109

theorem tailTrace_4006888 : CollatzResearch.WordTrace tailWord_4006888 prefixEnd_4006888 1371639648488416177315109 := by
  unfold tailWord_4006888
  simp only [CollatzResearch.WordTrace]
  refine ⟨73071605753868286416926659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97428807671824381889235545 73071605753868286416926659)
  ·
    refine ⟨109607408630802429625389989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73071605753868286416926659 109607408630802429625389989)
    ·
      refine ⟨20551389118275455554760623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109607408630802429625389989 20551389118275455554760623)
      ·
        refine ⟨30827083677413183332140935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20551389118275455554760623 30827083677413183332140935)
        ·
          refine ⟨46240625516119774998211403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30827083677413183332140935 46240625516119774998211403)
          ·
            refine ⟨69360938274179662497317105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46240625516119774998211403 69360938274179662497317105)
            ·
              refine ⟨52020703705634746872987829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69360938274179662497317105 52020703705634746872987829)
              ·
                refine ⟨4876940972403257519342609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52020703705634746872987829 4876940972403257519342609)
                ·
                  refine ⟨3657705729302443139506957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4876940972403257519342609 3657705729302443139506957)
                  ·
                    refine ⟨1371639648488416177315109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3657705729302443139506957 1371639648488416177315109)
                    ·
                      rfl

theorem cell22_4006888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_4006888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006888 prefixEnd_4006888 := by exact prefixLift 4006888
  have htrace : WordTrace (prefixWord ++ tailWord_4006888) baseStart_4006888 baseEnd_4006888 := by
    simpa [prefixWord, tailWord_4006888, baseEnd_4006888] using wordTrace_append hprefix tailTrace_4006888
  have hstable : (prefixWord ++ tailWord_4006888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006888).length < 2 ^ (prefixWord ++ tailWord_4006888).sum := by decide
  have hdescent : baseEnd_4006888 < baseStart_4006888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006900 : List Nat := [2, 6, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_4006900 : Nat := 118140960795 + 4006900 * 2 ^ 59
def prefixEnd_4006900 : Nat := 4983230072969 + 3 ^ 40 * 4006900 * 2
def baseEnd_4006900 : Nat := 1371643756333652146015073

theorem tailTrace_4006900 : CollatzResearch.WordTrace tailWord_4006900 prefixEnd_4006900 1371643756333652146015073 := by
  unfold tailWord_4006900
  simp only [CollatzResearch.WordTrace]
  refine ⟨73071824591846549441645077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97429099455795399255526769 73071824591846549441645077)
  ·
    refine ⟨3425241777742807005077113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73071824591846549441645077 3425241777742807005077113)
    ·
      refine ⟨2568931333307105253807835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3425241777742807005077113 2568931333307105253807835)
      ·
        refine ⟨3853396999960657880711753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2568931333307105253807835 3853396999960657880711753)
        ·
          refine ⟨2890047749970493410533815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3853396999960657880711753 2890047749970493410533815)
          ·
            refine ⟨4335071624955740115800723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2890047749970493410533815 4335071624955740115800723)
            ·
              refine ⟨6502607437433610173701085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4335071624955740115800723 6502607437433610173701085)
              ·
                refine ⟨2438477789037603815137907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6502607437433610173701085 2438477789037603815137907)
                ·
                  refine ⟨3657716683556405722706861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438477789037603815137907 3657716683556405722706861)
                  ·
                    refine ⟨1371643756333652146015073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3657716683556405722706861 1371643756333652146015073)
                    ·
                      rfl

theorem cell22_4006900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_4006900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4006900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4006900 prefixEnd_4006900 := by exact prefixLift 4006900
  have htrace : WordTrace (prefixWord ++ tailWord_4006900) baseStart_4006900 baseEnd_4006900 := by
    simpa [prefixWord, tailWord_4006900, baseEnd_4006900] using wordTrace_append hprefix tailTrace_4006900
  have hstable : (prefixWord ++ tailWord_4006900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006900).length < 2 ^ (prefixWord ++ tailWord_4006900).sum := by decide
  have hdescent : baseEnd_4006900 < baseStart_4006900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007010 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_4007010 : Nat := 118140960795 + 4007010 * 2 ^ 59
def prefixEnd_4007010 : Nat := 4983230072969 + 3 ^ 40 * 4007010 * 2
def baseEnd_4007010 : Nat := 1371681411581648525764735

theorem tailTrace_4007010 : CollatzResearch.WordTrace tailWord_4007010 prefixEnd_4007010 1371681411581648525764735 := by
  unfold tailWord_4007010
  simp only [CollatzResearch.WordTrace]
  refine ⟨36536915303323646917448621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97431774142196391779862989 36536915303323646917448621)
  ·
    refine ⟨13701343238746367594043233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36536915303323646917448621 13701343238746367594043233)
    ·
      refine ⟨10276007429059775695532425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13701343238746367594043233 10276007429059775695532425)
      ·
        refine ⟨7707005571794831771649319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10276007429059775695532425 7707005571794831771649319)
        ·
          refine ⟨11560508357692247657473979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7707005571794831771649319 11560508357692247657473979)
          ·
            refine ⟨17340762536538371486210969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11560508357692247657473979 17340762536538371486210969)
            ·
              refine ⟨13005571902403778614658227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17340762536538371486210969 13005571902403778614658227)
              ·
                refine ⟨19508357853605667921987341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13005571902403778614658227 19508357853605667921987341)
                ·
                  refine ⟨7315634195102125470745253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19508357853605667921987341 7315634195102125470745253)
                  ·
                    refine ⟨1371681411581648525764735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7315634195102125470745253 1371681411581648525764735)
                    ·
                      rfl

theorem cell22_4007010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_4007010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007010 prefixEnd_4007010 := by exact prefixLift 4007010
  have htrace : WordTrace (prefixWord ++ tailWord_4007010) baseStart_4007010 baseEnd_4007010 := by
    simpa [prefixWord, tailWord_4007010, baseEnd_4007010] using wordTrace_append hprefix tailTrace_4007010
  have hstable : (prefixWord ++ tailWord_4007010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007010).length < 2 ^ (prefixWord ++ tailWord_4007010).sum := by decide
  have hdescent : baseEnd_4007010 < baseStart_4007010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007023 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 4, 3]
def baseStart_4007023 : Nat := 118140960795 + 4007023 * 2 ^ 59
def prefixEnd_4007023 : Nat := 4983230072969 + 3 ^ 40 * 4007023 * 2
def baseEnd_4007023 : Nat := 1371685861747320825189695

theorem tailTrace_4007023 : CollatzResearch.WordTrace tailWord_4007023 prefixEnd_4007023 1371685861747320825189695 := by
  unfold tailWord_4007023
  simp only [CollatzResearch.WordTrace]
  refine ⟨146148135362247490890017723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97432090241498327260011815 146148135362247490890017723)
  ·
    refine ⟨219222203043371236335026585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146148135362247490890017723 219222203043371236335026585)
    ·
      refine ⟨164416652282528427251269939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219222203043371236335026585 164416652282528427251269939)
      ·
        refine ⟨246624978423792640876904909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164416652282528427251269939 246624978423792640876904909)
        ·
          refine ⟨92484366908922240328839341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246624978423792640876904909 92484366908922240328839341)
          ·
            refine ⟨34681637590845840123314753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92484366908922240328839341 34681637590845840123314753)
            ·
              refine ⟨26011228193134380092486065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34681637590845840123314753 26011228193134380092486065)
              ·
                refine ⟨19508421144850785069364549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26011228193134380092486065 19508421144850785069364549)
                ·
                  refine ⟨3657828964659522200505853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19508421144850785069364549 3657828964659522200505853)
                  ·
                    refine ⟨1371685861747320825189695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3657828964659522200505853 1371685861747320825189695)
                    ·
                      rfl

theorem cell22_4007023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 3].length) (baseStart_4007023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007023 prefixEnd_4007023 := by exact prefixLift 4007023
  have htrace : WordTrace (prefixWord ++ tailWord_4007023) baseStart_4007023 baseEnd_4007023 := by
    simpa [prefixWord, tailWord_4007023, baseEnd_4007023] using wordTrace_append hprefix tailTrace_4007023
  have hstable : (prefixWord ++ tailWord_4007023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007023).length < 2 ^ (prefixWord ++ tailWord_4007023).sum := by decide
  have hdescent : baseEnd_4007023 < baseStart_4007023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007036 : List Nat := [2, 2, 2, 1, 1, 3, 11]
def baseStart_4007036 : Nat := 118140960795 + 4007036 * 2 ^ 59
def prefixEnd_4007036 : Nat := 4983230072969 + 3 ^ 40 * 4007036 * 2
def baseEnd_4007036 : Nat := 50803344885666412022765

theorem tailTrace_4007036 : CollatzResearch.WordTrace tailWord_4007036 prefixEnd_4007036 50803344885666412022765 := by
  unfold tailWord_4007036
  simp only [CollatzResearch.WordTrace]
  refine ⟨73074304755600197055120481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97432406340800262740160641 73074304755600197055120481)
  ·
    refine ⟨54805728566700147791340361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73074304755600197055120481 54805728566700147791340361)
    ·
      refine ⟨41104296425025110843505271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54805728566700147791340361 41104296425025110843505271)
      ·
        refine ⟨61656444637537666265257907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41104296425025110843505271 61656444637537666265257907)
        ·
          refine ⟨92484666956306499397886861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61656444637537666265257907 92484666956306499397886861)
          ·
            refine ⟨34681750108614937274207573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92484666956306499397886861 34681750108614937274207573)
            ·
              refine ⟨50803344885666412022765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34681750108614937274207573 50803344885666412022765)
              ·
                rfl

theorem cell22_4007036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 11].length) (baseStart_4007036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007036 prefixEnd_4007036 := by exact prefixLift 4007036
  have htrace : WordTrace (prefixWord ++ tailWord_4007036) baseStart_4007036 baseEnd_4007036 := by
    simpa [prefixWord, tailWord_4007036, baseEnd_4007036] using wordTrace_append hprefix tailTrace_4007036
  have hstable : (prefixWord ++ tailWord_4007036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007036).length < 2 ^ (prefixWord ++ tailWord_4007036).sum := by decide
  have hdescent : baseEnd_4007036 < baseStart_4007036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007040 : List Nat := [2, 1, 1, 2, 1, 3, 5, 2, 2, 3]
def baseStart_4007040 : Nat := 118140960795 + 4007040 * 2 ^ 59
def prefixEnd_4007040 : Nat := 4983230072969 + 3 ^ 40 * 4007040 * 2
def baseEnd_4007040 : Nat := 1371691681194738447514643

theorem tailTrace_4007040 : CollatzResearch.WordTrace tailWord_4007040 prefixEnd_4007040 1371691681194738447514643 := by
  unfold tailWord_4007040
  simp only [CollatzResearch.WordTrace]
  refine ⟨73074377701592951396693287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97432503602123935195591049 73074377701592951396693287)
  ·
    refine ⟨109611566552389427095039931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73074377701592951396693287 109611566552389427095039931)
    ·
      refine ⟨164417349828584140642559897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109611566552389427095039931 164417349828584140642559897)
      ·
        refine ⟨123313012371438105481919923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164417349828584140642559897 123313012371438105481919923)
        ·
          refine ⟨184969518557157158222879885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123313012371438105481919923 184969518557157158222879885)
          ·
            refine ⟨69363569458933934333579957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184969518557157158222879885 69363569458933934333579957)
            ·
              refine ⟨6502834636775056343773121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69363569458933934333579957 6502834636775056343773121)
              ·
                refine ⟨4877125977581292257829841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6502834636775056343773121 4877125977581292257829841)
                ·
                  refine ⟨3657844483185969193372381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4877125977581292257829841 3657844483185969193372381)
                  ·
                    refine ⟨1371691681194738447514643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3657844483185969193372381 1371691681194738447514643)
                    ·
                      rfl

theorem cell22_4007040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 2, 3].length) (baseStart_4007040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007040 prefixEnd_4007040 := by exact prefixLift 4007040
  have htrace : WordTrace (prefixWord ++ tailWord_4007040) baseStart_4007040 baseEnd_4007040 := by
    simpa [prefixWord, tailWord_4007040, baseEnd_4007040] using wordTrace_append hprefix tailTrace_4007040
  have hstable : (prefixWord ++ tailWord_4007040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007040).length < 2 ^ (prefixWord ++ tailWord_4007040).sum := by decide
  have hdescent : baseEnd_4007040 < baseStart_4007040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007070 : List Nat := [4, 3, 1, 1, 2, 2, 1, 8]
def baseStart_4007070 : Nat := 118140960795 + 4007070 * 2 ^ 59
def prefixEnd_4007070 : Nat := 4983230072969 + 3 ^ 40 * 4007070 * 2
def baseEnd_4007070 : Nat := 152411327867536485473839

theorem tailTrace_4007070 : CollatzResearch.WordTrace tailWord_4007070 prefixEnd_4007070 152411327867536485473839 := by
  unfold tailWord_4007070
  simp only [CollatzResearch.WordTrace]
  refine ⟨18268731199134652239622333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97433233062051478611319109 18268731199134652239622333)
  ·
    refine ⟨6850774199675494589858375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18268731199134652239622333 6850774199675494589858375)
    ·
      refine ⟨10276161299513241884787563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6850774199675494589858375 10276161299513241884787563)
      ·
        refine ⟨15414241949269862827181345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10276161299513241884787563 15414241949269862827181345)
        ·
          refine ⟨11560681461952397120386009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15414241949269862827181345 11560681461952397120386009)
          ·
            refine ⟨8670511096464297840289507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11560681461952397120386009 8670511096464297840289507)
            ·
              refine ⟨13005766644696446760434261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8670511096464297840289507 13005766644696446760434261)
              ·
                refine ⟨152411327867536485473839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13005766644696446760434261 152411327867536485473839)
                ·
                  rfl

theorem cell22_4007070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_4007070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007070 prefixEnd_4007070 := by exact prefixLift 4007070
  have htrace : WordTrace (prefixWord ++ tailWord_4007070) baseStart_4007070 baseEnd_4007070 := by
    simpa [prefixWord, tailWord_4007070, baseEnd_4007070] using wordTrace_append hprefix tailTrace_4007070
  have hstable : (prefixWord ++ tailWord_4007070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007070).length < 2 ^ (prefixWord ++ tailWord_4007070).sum := by decide
  have hdescent : baseEnd_4007070 < baseStart_4007070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007098 : List Nat := [3, 1, 1, 1, 2, 2, 1, 6, 5]
def baseStart_4007098 : Nat := 118140960795 + 4007098 * 2 ^ 59
def prefixEnd_4007098 : Nat := 4983230072969 + 3 ^ 40 * 4007098 * 2
def baseEnd_4007098 : Nat := 457237178593348543188155

theorem tailTrace_4007098 : CollatzResearch.WordTrace tailWord_4007098 prefixEnd_4007098 457237178593348543188155 := by
  unfold tailWord_4007098
  simp only [CollatzResearch.WordTrace]
  refine ⟨36537717709243944674749487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97433913891317185799331965 36537717709243944674749487)
  ·
    refine ⟨54806576563865917012124231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36537717709243944674749487 54806576563865917012124231)
    ·
      refine ⟨82209864845798875518186347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54806576563865917012124231 82209864845798875518186347)
      ·
        refine ⟨123314797268698313277279521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82209864845798875518186347 123314797268698313277279521)
        ·
          refine ⟨92486097951523734957959641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123314797268698313277279521 92486097951523734957959641)
          ·
            refine ⟨69364573463642801218469731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92486097951523734957959641 69364573463642801218469731)
            ·
              refine ⟨104046860195464201827704597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69364573463642801218469731 104046860195464201827704597)
              ·
                refine ⟨4877196571662384460673653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104046860195464201827704597 4877196571662384460673653)
                ·
                  refine ⟨457237178593348543188155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4877196571662384460673653 457237178593348543188155)
                  ·
                    rfl

theorem cell22_4007098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_4007098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007098 prefixEnd_4007098 := by exact prefixLift 4007098
  have htrace : WordTrace (prefixWord ++ tailWord_4007098) baseStart_4007098 baseEnd_4007098 := by
    simpa [prefixWord, tailWord_4007098, baseEnd_4007098] using wordTrace_append hprefix tailTrace_4007098
  have hstable : (prefixWord ++ tailWord_4007098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007098).length < 2 ^ (prefixWord ++ tailWord_4007098).sum := by decide
  have hdescent : baseEnd_4007098 < baseStart_4007098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007102 : List Nat := [4, 2, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_4007102 : Nat := 118140960795 + 4007102 * 2 ^ 59
def prefixEnd_4007102 : Nat := 4983230072969 + 3 ^ 40 * 4007102 * 2
def baseEnd_4007102 : Nat := 1371712905061790952464453

theorem tailTrace_4007102 : CollatzResearch.WordTrace tailWord_4007102 prefixEnd_4007102 1371712905061790952464453 := by
  unfold tailWord_4007102
  simp only [CollatzResearch.WordTrace]
  refine ⟨18268877091120160922767945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97434011152640858254762373 18268877091120160922767945)
  ·
    refine ⟨13701657818340120692075959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18268877091120160922767945 13701657818340120692075959)
    ·
      refine ⟨20552486727510181038113939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13701657818340120692075959 20552486727510181038113939)
      ·
        refine ⟨30828730091265271557170909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20552486727510181038113939 30828730091265271557170909)
        ·
          refine ⟨11560773784224476833939091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30828730091265271557170909 11560773784224476833939091)
          ·
            refine ⟨17341160676336715250908637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11560773784224476833939091 17341160676336715250908637)
            ·
              refine ⟨6502935253626268219090739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17341160676336715250908637 6502935253626268219090739)
              ·
                refine ⟨9754402880439402328636109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6502935253626268219090739 9754402880439402328636109)
                ·
                  refine ⟨3657901080164775873238541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9754402880439402328636109 3657901080164775873238541)
                  ·
                    refine ⟨1371712905061790952464453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3657901080164775873238541 1371712905061790952464453)
                    ·
                      rfl

theorem cell22_4007102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_4007102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007102 prefixEnd_4007102 := by exact prefixLift 4007102
  have htrace : WordTrace (prefixWord ++ tailWord_4007102) baseStart_4007102 baseEnd_4007102 := by
    simpa [prefixWord, tailWord_4007102, baseEnd_4007102] using wordTrace_append hprefix tailTrace_4007102
  have hstable : (prefixWord ++ tailWord_4007102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007102).length < 2 ^ (prefixWord ++ tailWord_4007102).sum := by decide
  have hdescent : baseEnd_4007102 < baseStart_4007102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007173 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 1, 6]
def baseStart_4007173 : Nat := 118140960795 + 4007173 * 2 ^ 59
def prefixEnd_4007173 : Nat := 4983230072969 + 3 ^ 40 * 4007173 * 2
def baseEnd_4007173 : Nat := 1371737209812770433939235

theorem tailTrace_4007173 : CollatzResearch.WordTrace tailWord_4007173 prefixEnd_4007173 1371737209812770433939235 := by
  unfold tailWord_4007173
  simp only [CollatzResearch.WordTrace]
  refine ⟨146153606311704066507978173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97435737541136044338652115 146153606311704066507978173)
  ·
    refine ⟨54807602366889024940491815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146153606311704066507978173 54807602366889024940491815)
    ·
      refine ⟨82211403550333537410737723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54807602366889024940491815 82211403550333537410737723)
      ·
        refine ⟨123317105325500306116106585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82211403550333537410737723 123317105325500306116106585)
        ·
          refine ⟨92487828994125229587079939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123317105325500306116106585 92487828994125229587079939)
          ·
            refine ⟨138731743491187844380619909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92487828994125229587079939 138731743491187844380619909)
            ·
              refine ⟨26012201904597720821366233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138731743491187844380619909 26012201904597720821366233)
              ·
                refine ⟨19509151428448290616024675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26012201904597720821366233 19509151428448290616024675)
                ·
                  refine ⟨29263727142672435924037013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19509151428448290616024675 29263727142672435924037013)
                  ·
                    refine ⟨1371737209812770433939235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29263727142672435924037013 1371737209812770433939235)
                    ·
                      rfl

theorem cell22_4007173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_4007173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007173 prefixEnd_4007173 := by exact prefixLift 4007173
  have htrace : WordTrace (prefixWord ++ tailWord_4007173) baseStart_4007173 baseEnd_4007173 := by
    simpa [prefixWord, tailWord_4007173, baseEnd_4007173] using wordTrace_append hprefix tailTrace_4007173
  have hstable : (prefixWord ++ tailWord_4007173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007173).length < 2 ^ (prefixWord ++ tailWord_4007173).sum := by decide
  have hdescent : baseEnd_4007173 < baseStart_4007173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007271 : List Nat := [1, 1, 5, 1, 5, 1, 1, 1, 3, 3]
def baseStart_4007271 : Nat := 118140960795 + 4007271 * 2 ^ 59
def prefixEnd_4007271 : Nat := 4983230072969 + 3 ^ 40 * 4007271 * 2
def baseEnd_4007271 : Nat := 1371770757215530844988935

theorem tailTrace_4007271 : CollatzResearch.WordTrace tailWord_4007271 prefixEnd_4007271 1371770757215530844988935 := by
  unfold tailWord_4007271
  simp only [CollatzResearch.WordTrace]
  refine ⟨146157180665349029245045667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97438120443566019496697111 146157180665349029245045667)
  ·
    refine ⟨219235770998023543867568501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146157180665349029245045667 219235770998023543867568501)
    ·
      refine ⟨20553353531064707237584547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219235770998023543867568501 20553353531064707237584547)
      ·
        refine ⟨30830030296597060856376821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20553353531064707237584547 30830030296597060856376821)
        ·
          refine ⟨2890315340305974455285327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30830030296597060856376821 2890315340305974455285327)
          ·
            refine ⟨4335473010458961682927991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2890315340305974455285327 4335473010458961682927991)
            ·
              refine ⟨6503209515688442524391987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4335473010458961682927991 6503209515688442524391987)
              ·
                refine ⟨9754814273532663786587981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6503209515688442524391987 9754814273532663786587981)
                ·
                  refine ⟨3658055352574748919970493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9754814273532663786587981 3658055352574748919970493)
                  ·
                    refine ⟨1371770757215530844988935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3658055352574748919970493 1371770757215530844988935)
                    ·
                      rfl

theorem cell22_4007271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_4007271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007271 prefixEnd_4007271 := by exact prefixLift 4007271
  have htrace : WordTrace (prefixWord ++ tailWord_4007271) baseStart_4007271 baseEnd_4007271 := by
    simpa [prefixWord, tailWord_4007271, baseEnd_4007271] using wordTrace_append hprefix tailTrace_4007271
  have hstable : (prefixWord ++ tailWord_4007271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007271).length < 2 ^ (prefixWord ++ tailWord_4007271).sum := by decide
  have hdescent : baseEnd_4007271 < baseStart_4007271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007280 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 3, 4]
def baseStart_4007280 : Nat := 118140960795 + 4007280 * 2 ^ 59
def prefixEnd_4007280 : Nat := 4983230072969 + 3 ^ 40 * 4007280 * 2
def baseEnd_4007280 : Nat := 1371773838099457821513907

theorem tailTrace_4007280 : CollatzResearch.WordTrace tailWord_4007280 prefixEnd_4007280 1371773838099457821513907 := by
  unfold tailWord_4007280
  simp only [CollatzResearch.WordTrace]
  refine ⟨73078754461158211891061647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97438339281544282521415529 73078754461158211891061647)
  ·
    refine ⟨109618131691737317836592471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73078754461158211891061647 109618131691737317836592471)
    ·
      refine ⟨164427197537605976754888707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109618131691737317836592471 164427197537605976754888707)
      ·
        refine ⟨246640796306408965132333061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164427197537605976754888707 246640796306408965132333061)
        ·
          refine ⟨46245149307451680962312449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246640796306408965132333061 46245149307451680962312449)
          ·
            refine ⟨34683861980588760721734337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46245149307451680962312449 34683861980588760721734337)
            ·
              refine ⟨26012896485441570541300753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34683861980588760721734337 26012896485441570541300753)
              ·
                refine ⟨19509672364081177905975565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26012896485441570541300753 19509672364081177905975565)
                ·
                  refine ⟨7316127136530441714740837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19509672364081177905975565 7316127136530441714740837)
                  ·
                    refine ⟨1371773838099457821513907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7316127136530441714740837 1371773838099457821513907)
                    ·
                      rfl

theorem cell22_4007280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_4007280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007280 prefixEnd_4007280 := by exact prefixLift 4007280
  have htrace : WordTrace (prefixWord ++ tailWord_4007280) baseStart_4007280 baseEnd_4007280 := by
    simpa [prefixWord, tailWord_4007280, baseEnd_4007280] using wordTrace_append hprefix tailTrace_4007280
  have hstable : (prefixWord ++ tailWord_4007280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007280).length < 2 ^ (prefixWord ++ tailWord_4007280).sum := by decide
  have hdescent : baseEnd_4007280 < baseStart_4007280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007340 : List Nat := [2, 2, 1, 1, 1, 1, 7, 7]
def baseStart_4007340 : Nat := 118140960795 + 4007340 * 2 ^ 59
def prefixEnd_4007340 : Nat := 4983230072969 + 3 ^ 40 * 4007340 * 2
def baseEnd_4007340 : Nat := 152421597480626407223747

theorem tailTrace_4007340 : CollatzResearch.WordTrace tailWord_4007340 prefixEnd_4007340 152421597480626407223747 := by
  unfold tailWord_4007340
  simp only [CollatzResearch.WordTrace]
  refine ⟨73079848651049527014653737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97439798201399369352871649 73079848651049527014653737)
  ·
    refine ⟨54809886488287145260990303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73079848651049527014653737 54809886488287145260990303)
    ·
      refine ⟨82214829732430717891485455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54809886488287145260990303 82214829732430717891485455)
      ·
        refine ⟨123322244598646076837228183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82214829732430717891485455 123322244598646076837228183)
        ·
          refine ⟨184983366897969115255842275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123322244598646076837228183 184983366897969115255842275)
          ·
            refine ⟨277475050346953672883763413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184983366897969115255842275 277475050346953672883763413)
            ·
              refine ⟨6503321492506726708213205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 277475050346953672883763413 6503321492506726708213205)
              ·
                refine ⟨152421597480626407223747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6503321492506726708213205 152421597480626407223747)
                ·
                  rfl

theorem cell22_4007340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 7].length) (baseStart_4007340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007340 prefixEnd_4007340 := by exact prefixLift 4007340
  have htrace : WordTrace (prefixWord ++ tailWord_4007340) baseStart_4007340 baseEnd_4007340 := by
    simpa [prefixWord, tailWord_4007340, baseEnd_4007340] using wordTrace_append hprefix tailTrace_4007340
  have hstable : (prefixWord ++ tailWord_4007340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007340).length < 2 ^ (prefixWord ++ tailWord_4007340).sum := by decide
  have hdescent : baseEnd_4007340 < baseStart_4007340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007357 : List Nat := [1, 4, 1, 2, 2, 1, 5, 6]
def baseStart_4007357 : Nat := 118140960795 + 4007357 * 2 ^ 59
def prefixEnd_4007357 : Nat := 4983230072969 + 3 ^ 40 * 4007357 * 2
def baseEnd_4007357 : Nat := 152422244085895031926519

theorem tailTrace_4007357 : CollatzResearch.WordTrace tailWord_4007357 prefixEnd_4007357 152422244085895031926519 := by
  unfold tailWord_4007357
  simp only [CollatzResearch.WordTrace]
  refine ⟨146160317343037465932676325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97440211562024977288450883 146160317343037465932676325)
  ·
    refine ⟨27405059501819524862376811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146160317343037465932676325 27405059501819524862376811)
    ·
      refine ⟨41107589252729287293565217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27405059501819524862376811 41107589252729287293565217)
      ·
        refine ⟨30830691939546965470173913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41107589252729287293565217 30830691939546965470173913)
        ·
          refine ⟨23123018954660224102630435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30830691939546965470173913 23123018954660224102630435)
          ·
            refine ⟨34684528431990336153945653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23123018954660224102630435 34684528431990336153945653)
            ·
              refine ⟨3251674540499094014432405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34684528431990336153945653 3251674540499094014432405)
              ·
                refine ⟨152422244085895031926519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3251674540499094014432405 152422244085895031926519)
                ·
                  rfl

theorem cell22_4007357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 6].length) (baseStart_4007357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007357 prefixEnd_4007357 := by exact prefixLift 4007357
  have htrace : WordTrace (prefixWord ++ tailWord_4007357) baseStart_4007357 baseEnd_4007357 := by
    simpa [prefixWord, tailWord_4007357, baseEnd_4007357] using wordTrace_append hprefix tailTrace_4007357
  have hstable : (prefixWord ++ tailWord_4007357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007357).length < 2 ^ (prefixWord ++ tailWord_4007357).sum := by decide
  have hdescent : baseEnd_4007357 < baseStart_4007357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007389 : List Nat := [1, 4, 3, 1, 1, 2, 1, 3, 3, 3]
def baseStart_4007389 : Nat := 118140960795 + 4007389 * 2 ^ 59
def prefixEnd_4007389 : Nat := 4983230072969 + 3 ^ 40 * 4007389 * 2
def baseEnd_4007389 : Nat := 1371811151027017870538573

theorem tailTrace_4007389 : CollatzResearch.WordTrace tailWord_4007389 prefixEnd_4007389 1371811151027017870538573 := by
  unfold tailWord_4007389
  simp only [CollatzResearch.WordTrace]
  refine ⟨146161484478921535397841221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97440989652614356931894147 146161484478921535397841221)
  ·
    refine ⟨27405278339797787887095229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146161484478921535397841221 27405278339797787887095229)
    ·
      refine ⟨10276979377424170457660711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27405278339797787887095229 10276979377424170457660711)
      ·
        refine ⟨15415469066136255686491067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10276979377424170457660711 15415469066136255686491067)
        ·
          refine ⟨23123203599204383529736601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15415469066136255686491067 23123203599204383529736601)
          ·
            refine ⟨17342402699403287647302451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23123203599204383529736601 17342402699403287647302451)
            ·
              refine ⟨26013604049104931470953677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17342402699403287647302451 26013604049104931470953677)
              ·
                refine ⟨9755101518414349301607629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26013604049104931470953677 9755101518414349301607629)
                ·
                  refine ⟨3658163069405380988102861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9755101518414349301607629 3658163069405380988102861)
                  ·
                    refine ⟨1371811151027017870538573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3658163069405380988102861 1371811151027017870538573)
                    ·
                      rfl

theorem cell22_4007389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_4007389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007389 prefixEnd_4007389 := by exact prefixLift 4007389
  have htrace : WordTrace (prefixWord ++ tailWord_4007389) baseStart_4007389 baseEnd_4007389 := by
    simpa [prefixWord, tailWord_4007389, baseEnd_4007389] using wordTrace_append hprefix tailTrace_4007389
  have hstable : (prefixWord ++ tailWord_4007389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007389).length < 2 ^ (prefixWord ++ tailWord_4007389).sum := by decide
  have hdescent : baseEnd_4007389 < baseStart_4007389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007524 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 5, 3]
def baseStart_4007524 : Nat := 118140960795 + 4007524 * 2 ^ 59
def prefixEnd_4007524 : Nat := 4983230072969 + 3 ^ 40 * 4007524 * 2
def baseEnd_4007524 : Nat := 1371857364285922518413159

theorem tailTrace_4007524 : CollatzResearch.WordTrace tailWord_4007524 prefixEnd_4007524 1371857364285922518413159 := by
  unfold tailWord_4007524
  simp only [CollatzResearch.WordTrace]
  refine ⟨73083204166716226727002813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97444272222288302302670417 73083204166716226727002813)
  ·
    refine ⟨27406201562518585022626055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73083204166716226727002813 27406201562518585022626055)
    ·
      refine ⟨41109302343777877533939083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27406201562518585022626055 41109302343777877533939083)
      ·
        refine ⟨61663953515666816300908625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41109302343777877533939083 61663953515666816300908625)
        ·
          refine ⟨46247965136750112225681469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61663953515666816300908625 46247965136750112225681469)
          ·
            refine ⟨17342986926281292084630551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46247965136750112225681469 17342986926281292084630551)
            ·
              refine ⟨26014480389421938126945827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17342986926281292084630551 26014480389421938126945827)
              ·
                refine ⟨39021720584132907190418741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26014480389421938126945827 39021720584132907190418741)
                ·
                  refine ⟨3658286304762460049101757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39021720584132907190418741 3658286304762460049101757)
                  ·
                    refine ⟨1371857364285922518413159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3658286304762460049101757 1371857364285922518413159)
                    ·
                      rfl

theorem cell22_4007524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_4007524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007524 prefixEnd_4007524 := by exact prefixLift 4007524
  have htrace : WordTrace (prefixWord ++ tailWord_4007524) baseStart_4007524 baseEnd_4007524 := by
    simpa [prefixWord, tailWord_4007524, baseEnd_4007524] using wordTrace_append hprefix tailTrace_4007524
  have hstable : (prefixWord ++ tailWord_4007524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007524).length < 2 ^ (prefixWord ++ tailWord_4007524).sum := by decide
  have hdescent : baseEnd_4007524 < baseStart_4007524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007552 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 4, 5]
def baseStart_4007552 : Nat := 118140960795 + 4007552 * 2 ^ 59
def prefixEnd_4007552 : Nat := 4983230072969 + 3 ^ 40 * 4007552 * 2
def baseEnd_4007552 : Nat := 1371866949258139778713073

theorem tailTrace_4007552 : CollatzResearch.WordTrace tailWord_4007552 prefixEnd_4007552 1371866949258139778713073 := by
  unfold tailWord_4007552
  simp only [CollatzResearch.WordTrace]
  refine ⟨73083714788665507118012455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97444953051554009490683273 73083714788665507118012455)
  ·
    refine ⟨109625572182998260677018683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73083714788665507118012455 109625572182998260677018683)
    ·
      refine ⟨164438358274497391015528025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109625572182998260677018683 164438358274497391015528025)
      ·
        refine ⟨123328768705873043261646019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164438358274497391015528025 123328768705873043261646019)
        ·
          refine ⟨184993153058809564892469029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123328768705873043261646019 184993153058809564892469029)
          ·
            refine ⟨34686216198526793417337943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184993153058809564892469029 34686216198526793417337943)
            ·
              refine ⟨52029324297790190126006915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34686216198526793417337943 52029324297790190126006915)
              ·
                refine ⟨78043986446685285189010373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52029324297790190126006915 78043986446685285189010373)
                ·
                  refine ⟨14633247458753490972939445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78043986446685285189010373 14633247458753490972939445)
                  ·
                    refine ⟨1371866949258139778713073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14633247458753490972939445 1371866949258139778713073)
                    ·
                      rfl

theorem cell22_4007552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_4007552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007552 prefixEnd_4007552 := by exact prefixLift 4007552
  have htrace : WordTrace (prefixWord ++ tailWord_4007552) baseStart_4007552 baseEnd_4007552 := by
    simpa [prefixWord, tailWord_4007552, baseEnd_4007552] using wordTrace_append hprefix tailTrace_4007552
  have hstable : (prefixWord ++ tailWord_4007552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007552).length < 2 ^ (prefixWord ++ tailWord_4007552).sum := by decide
  have hdescent : baseEnd_4007552 < baseStart_4007552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007622 : List Nat := [6, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_4007622 : Nat := 118140960795 + 4007622 * 2 ^ 59
def prefixEnd_4007622 : Nat := 4983230072969 + 3 ^ 40 * 4007622 * 2
def baseEnd_4007622 : Nat := 457296970562894309820953

theorem tailTrace_4007622 : CollatzResearch.WordTrace tailWord_4007622 prefixEnd_4007622 457296970562894309820953 := by
  unfold tailWord_4007622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4567811958971169255971035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97446655124718277460715413 4567811958971169255971035)
  ·
    refine ⟨6851717938456753883956553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4567811958971169255971035 6851717938456753883956553)
    ·
      refine ⟨5138788453842565412967415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6851717938456753883956553 5138788453842565412967415)
      ·
        refine ⟨7708182680763848119451123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5138788453842565412967415 7708182680763848119451123)
        ·
          refine ⟨11562274021145772179176685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7708182680763848119451123 11562274021145772179176685)
          ·
            refine ⟨4335852757929664567191257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11562274021145772179176685 4335852757929664567191257)
            ·
              refine ⟨3251889568447248425393443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4335852757929664567191257 3251889568447248425393443)
              ·
                refine ⟨4877834352670872638090165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3251889568447248425393443 4877834352670872638090165)
                ·
                  refine ⟨457296970562894309820953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4877834352670872638090165 457296970562894309820953)
                  ·
                    rfl

theorem cell22_4007622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_4007622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007622 prefixEnd_4007622 := by exact prefixLift 4007622
  have htrace : WordTrace (prefixWord ++ tailWord_4007622) baseStart_4007622 baseEnd_4007622 := by
    simpa [prefixWord, tailWord_4007622, baseEnd_4007622] using wordTrace_append hprefix tailTrace_4007622
  have hstable : (prefixWord ++ tailWord_4007622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007622).length < 2 ^ (prefixWord ++ tailWord_4007622).sum := by decide
  have hdescent : baseEnd_4007622 < baseStart_4007622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007676 : List Nat := [2, 2, 2, 1, 3, 1, 2, 3, 3, 3]
def baseStart_4007676 : Nat := 118140960795 + 4007676 * 2 ^ 59
def prefixEnd_4007676 : Nat := 4983230072969 + 3 ^ 40 * 4007676 * 2
def baseEnd_4007676 : Nat := 1371909396992244788612693

theorem tailTrace_4007676 : CollatzResearch.WordTrace tailWord_4007676 prefixEnd_4007676 1371909396992244788612693 := by
  unfold tailWord_4007676
  simp only [CollatzResearch.WordTrace]
  refine ⟨73085976114440891706769441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97447968152587855609025921 73085976114440891706769441)
  ·
    refine ⟨54814482085830668780077081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73085976114440891706769441 54814482085830668780077081)
    ·
      refine ⟨41110861564373001585057811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54814482085830668780077081 41110861564373001585057811)
      ·
        refine ⟨61666292346559502377586717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41110861564373001585057811 61666292346559502377586717)
        ·
          refine ⟨23124859629959813391595019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61666292346559502377586717 23124859629959813391595019)
          ·
            refine ⟨34687289444939720087392529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23124859629959813391595019 34687289444939720087392529)
            ·
              refine ⟨26015467083704790065544397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34687289444939720087392529 26015467083704790065544397)
              ·
                refine ⟨9755800156389296274579149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26015467083704790065544397 9755800156389296274579149)
                ·
                  refine ⟨3658425058645986102967181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9755800156389296274579149 3658425058645986102967181)
                  ·
                    refine ⟨1371909396992244788612693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3658425058645986102967181 1371909396992244788612693)
                    ·
                      rfl

theorem cell22_4007676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_4007676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007676 prefixEnd_4007676 := by exact prefixLift 4007676
  have htrace : WordTrace (prefixWord ++ tailWord_4007676) baseStart_4007676 baseEnd_4007676 := by
    simpa [prefixWord, tailWord_4007676, baseEnd_4007676] using wordTrace_append hprefix tailTrace_4007676
  have hstable : (prefixWord ++ tailWord_4007676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007676).length < 2 ^ (prefixWord ++ tailWord_4007676).sum := by decide
  have hdescent : baseEnd_4007676 < baseStart_4007676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007678 : List Nat := [4, 2, 2, 1, 3, 2, 1, 7]
def baseStart_4007678 : Nat := 118140960795 + 4007678 * 2 ^ 59
def prefixEnd_4007678 : Nat := 4983230072969 + 3 ^ 40 * 4007678 * 2
def baseEnd_4007678 : Nat := 152434453514790827784743

theorem tailTrace_4007678 : CollatzResearch.WordTrace tailWord_4007678 prefixEnd_4007678 152434453514790827784743 := by
  unfold tailWord_4007678
  simp only [CollatzResearch.WordTrace]
  refine ⟨18271503146859317219388961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97448016783249691836741125 18271503146859317219388961)
  ·
    refine ⟨13703627360144487914541721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18271503146859317219388961 13703627360144487914541721)
    ·
      refine ⟨10277720520108365935906291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13703627360144487914541721 10277720520108365935906291)
      ·
        refine ⟨15416580780162548903859437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10277720520108365935906291 15416580780162548903859437)
        ·
          refine ⟨5781217792560955838947289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15416580780162548903859437 5781217792560955838947289)
          ·
            refine ⟨4335913344420716879210467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5781217792560955838947289 4335913344420716879210467)
            ·
              refine ⟨6503870016631075318815701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4335913344420716879210467 6503870016631075318815701)
              ·
                refine ⟨152434453514790827784743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6503870016631075318815701 152434453514790827784743)
                ·
                  rfl

theorem cell22_4007678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_4007678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007678 prefixEnd_4007678 := by exact prefixLift 4007678
  have htrace : WordTrace (prefixWord ++ tailWord_4007678) baseStart_4007678 baseEnd_4007678 := by
    simpa [prefixWord, tailWord_4007678, baseEnd_4007678] using wordTrace_append hprefix tailTrace_4007678
  have hstable : (prefixWord ++ tailWord_4007678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007678).length < 2 ^ (prefixWord ++ tailWord_4007678).sum := by decide
  have hdescent : baseEnd_4007678 < baseStart_4007678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007783 : List Nat := [1, 1, 5, 1, 2, 1, 2, 4, 2, 3]
def baseStart_4007783 : Nat := 118140960795 + 4007783 * 2 ^ 59
def prefixEnd_4007783 : Nat := 4983230072969 + 3 ^ 40 * 4007783 * 2
def baseEnd_4007783 : Nat := 1371946025278932176187365

theorem tailTrace_4007783 : CollatzResearch.WordTrace tailWord_4007783 prefixEnd_4007783 1371946025278932176187365 := by
  unfold tailWord_4007783
  simp only [CollatzResearch.WordTrace]
  refine ⟨146175854839494140687684003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97450569892996093791789335 146175854839494140687684003)
  ·
    refine ⟨219263782259241211031526005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146175854839494140687684003 219263782259241211031526005)
    ·
      refine ⟨20555979586803863534205563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219263782259241211031526005 20555979586803863534205563)
      ·
        refine ⟨30833969380205795301308345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20555979586803863534205563 30833969380205795301308345)
        ·
          refine ⟨23125477035154346475981259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30833969380205795301308345 23125477035154346475981259)
          ·
            refine ⟨34688215552731519713971889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23125477035154346475981259 34688215552731519713971889)
            ·
              refine ⟨26016161664548639785478917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34688215552731519713971889 26016161664548639785478917)
              ·
                refine ⟨4878030312102869959777297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26016161664548639785478917 4878030312102869959777297)
                ·
                  refine ⟨3658522734077152469832973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4878030312102869959777297 3658522734077152469832973)
                  ·
                    refine ⟨1371946025278932176187365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3658522734077152469832973 1371946025278932176187365)
                    ·
                      rfl

theorem cell22_4007783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_4007783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007783 prefixEnd_4007783 := by exact prefixLift 4007783
  have htrace : WordTrace (prefixWord ++ tailWord_4007783) baseStart_4007783 baseEnd_4007783 := by
    simpa [prefixWord, tailWord_4007783, baseEnd_4007783] using wordTrace_append hprefix tailTrace_4007783
  have hstable : (prefixWord ++ tailWord_4007783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007783).length < 2 ^ (prefixWord ++ tailWord_4007783).sum := by decide
  have hdescent : baseEnd_4007783 < baseStart_4007783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007830 : List Nat := [5, 3, 1, 1, 2, 10]
def baseStart_4007830 : Nat := 118140960795 + 4007830 * 2 ^ 59
def prefixEnd_4007830 : Nat := 4983230072969 + 3 ^ 40 * 4007830 * 2
def baseEnd_4007830 : Nat := 16937803880733823706941

theorem tailTrace_4007830 : CollatzResearch.WordTrace tailWord_4007830 prefixEnd_4007830 16937803880733823706941 := by
  unfold tailWord_4007830
  simp only [CollatzResearch.WordTrace]
  refine ⟨9136098066895241732165309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97451712713549245143096629 9136098066895241732165309)
  ·
    refine ⟨3426036775085715649561991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9136098066895241732165309 3426036775085715649561991)
    ·
      refine ⟨5139055162628573474342987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3426036775085715649561991 5139055162628573474342987)
      ·
        refine ⟨7708582743942860211514481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5139055162628573474342987 7708582743942860211514481)
        ·
          refine ⟨5781437057957145158635861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7708582743942860211514481 5781437057957145158635861)
          ·
            refine ⟨16937803880733823706941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5781437057957145158635861 16937803880733823706941)
            ·
              rfl

theorem cell22_4007830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 10].length) (baseStart_4007830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007830 prefixEnd_4007830 := by exact prefixLift 4007830
  have htrace : WordTrace (prefixWord ++ tailWord_4007830) baseStart_4007830 baseEnd_4007830 := by
    simpa [prefixWord, tailWord_4007830, baseEnd_4007830] using wordTrace_append hprefix tailTrace_4007830
  have hstable : (prefixWord ++ tailWord_4007830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007830).length < 2 ^ (prefixWord ++ tailWord_4007830).sum := by decide
  have hdescent : baseEnd_4007830 < baseStart_4007830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007871 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 3, 4]
def baseStart_4007871 : Nat := 118140960795 + 4007871 * 2 ^ 59
def prefixEnd_4007871 : Nat := 4983230072969 + 3 ^ 40 * 4007871 * 2
def baseEnd_4007871 : Nat := 1371976149477329279987095

theorem tailTrace_4007871 : CollatzResearch.WordTrace tailWord_4007871 prefixEnd_4007871 1371976149477329279987095 := by
  unfold tailWord_4007871
  simp only [CollatzResearch.WordTrace]
  refine ⟨146179064463175331716887467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97452709642116887811258311 146179064463175331716887467)
  ·
    refine ⟨219268596694762997575331201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146179064463175331716887467 219268596694762997575331201)
    ·
      refine ⟨164451447521072248181498401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219268596694762997575331201 164451447521072248181498401)
      ·
        refine ⟨123338585640804186136123801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164451447521072248181498401 123338585640804186136123801)
        ·
          refine ⟨92503939230603139602092851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123338585640804186136123801 92503939230603139602092851)
          ·
            refine ⟨138755908845904709403139277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92503939230603139602092851 138755908845904709403139277)
            ·
              refine ⟨52033465817214266026177229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138755908845904709403139277 52033465817214266026177229)
              ·
                refine ⟨19512549681455349759816461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52033465817214266026177229 19512549681455349759816461)
                ·
                  refine ⟨7317206130545756159931173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19512549681455349759816461 7317206130545756159931173)
                  ·
                    refine ⟨1371976149477329279987095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7317206130545756159931173 1371976149477329279987095)
                    ·
                      rfl

theorem cell22_4007871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_4007871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007871 prefixEnd_4007871 := by exact prefixLift 4007871
  have htrace : WordTrace (prefixWord ++ tailWord_4007871) baseStart_4007871 baseEnd_4007871 := by
    simpa [prefixWord, tailWord_4007871, baseEnd_4007871] using wordTrace_append hprefix tailTrace_4007871
  have hstable : (prefixWord ++ tailWord_4007871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007871).length < 2 ^ (prefixWord ++ tailWord_4007871).sum := by decide
  have hdescent : baseEnd_4007871 < baseStart_4007871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007886 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 8]
def baseStart_4007886 : Nat := 118140960795 + 4007886 * 2 ^ 59
def prefixEnd_4007886 : Nat := 4983230072969 + 3 ^ 40 * 4007886 * 2
def baseEnd_4007886 : Nat := 457327094761291413620683

theorem tailTrace_4007886 : CollatzResearch.WordTrace tailWord_4007886 prefixEnd_4007886 457327094761291413620683 := by
  unfold tailWord_4007886
  simp only [CollatzResearch.WordTrace]
  refine ⟨18272451444765123659835439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97453074372080659519122341 18272451444765123659835439)
  ·
    refine ⟨27408677167147685489753159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18272451444765123659835439 27408677167147685489753159)
    ·
      refine ⟨41113015750721528234629739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27408677167147685489753159 41113015750721528234629739)
      ·
        refine ⟨61669523626082292351944609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41113015750721528234629739 61669523626082292351944609)
        ·
          refine ⟨46252142719561719263958457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61669523626082292351944609 46252142719561719263958457)
          ·
            refine ⟨34689107039671289447968843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46252142719561719263958457 34689107039671289447968843)
            ·
              refine ⟨52033660559506934171953265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34689107039671289447968843 52033660559506934171953265)
              ·
                refine ⟨39025245419630200628964949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52033660559506934171953265 39025245419630200628964949)
                ·
                  refine ⟨457327094761291413620683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39025245419630200628964949 457327094761291413620683)
                  ·
                    rfl

theorem cell22_4007886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_4007886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007886 prefixEnd_4007886 := by exact prefixLift 4007886
  have htrace : WordTrace (prefixWord ++ tailWord_4007886) baseStart_4007886 baseEnd_4007886 := by
    simpa [prefixWord, tailWord_4007886, baseEnd_4007886] using wordTrace_append hprefix tailTrace_4007886
  have hstable : (prefixWord ++ tailWord_4007886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007886).length < 2 ^ (prefixWord ++ tailWord_4007886).sum := by decide
  have hdescent : baseEnd_4007886 < baseStart_4007886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007903 : List Nat := [1, 1, 2, 3, 4, 2, 2, 1, 6]
def baseStart_4007903 : Nat := 118140960795 + 4007903 * 2 ^ 59
def prefixEnd_4007903 : Nat := 4983230072969 + 3 ^ 40 * 4007903 * 2
def baseEnd_4007903 : Nat := 457329034577097287728999

theorem tailTrace_4007903 : CollatzResearch.WordTrace tailWord_4007903 prefixEnd_4007903 457329034577097287728999 := by
  unfold tailWord_4007903
  simp only [CollatzResearch.WordTrace]
  refine ⟨146180231599059401182052363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97453487732706267454701575 146180231599059401182052363)
  ·
    refine ⟨219270347398589101773078545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146180231599059401182052363 219270347398589101773078545)
    ·
      refine ⟨164452760548941826329808909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219270347398589101773078545 164452760548941826329808909)
      ·
        refine ⟨61669785205853184873678341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164452760548941826329808909 61669785205853184873678341)
        ·
          refine ⟨11563084726097472163814689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61669785205853184873678341 11563084726097472163814689)
          ·
            refine ⟨8672313544573104122861017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11563084726097472163814689 8672313544573104122861017)
            ·
              refine ⟨6504235158429828092145763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8672313544573104122861017 6504235158429828092145763)
              ·
                refine ⟨9756352737644742138218645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6504235158429828092145763 9756352737644742138218645)
                ·
                  refine ⟨457329034577097287728999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9756352737644742138218645 457329034577097287728999)
                  ·
                    rfl

theorem cell22_4007903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 6].length) (baseStart_4007903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007903 prefixEnd_4007903 := by exact prefixLift 4007903
  have htrace : WordTrace (prefixWord ++ tailWord_4007903) baseStart_4007903 baseEnd_4007903 := by
    simpa [prefixWord, tailWord_4007903, baseEnd_4007903] using wordTrace_append hprefix tailTrace_4007903
  have hstable : (prefixWord ++ tailWord_4007903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007903).length < 2 ^ (prefixWord ++ tailWord_4007903).sum := by decide
  have hdescent : baseEnd_4007903 < baseStart_4007903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007961 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 2, 6]
def baseStart_4007961 : Nat := 118140960795 + 4007961 * 2 ^ 59
def prefixEnd_4007961 : Nat := 4983230072969 + 3 ^ 40 * 4007961 * 2
def baseEnd_4007961 : Nat := 1372006958316599045236819

theorem tailTrace_4007961 : CollatzResearch.WordTrace tailWord_4007961 prefixEnd_4007961 1372006958316599045236819 := by
  unfold tailWord_4007961
  simp only [CollatzResearch.WordTrace]
  refine ⟨146182347032849277087663737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97454898021899518058442491 146182347032849277087663737)
  ·
    refine ⟨109636760274636957815747803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146182347032849277087663737 109636760274636957815747803)
    ·
      refine ⟨164455140411955436723621705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109636760274636957815747803 164455140411955436723621705)
      ·
        refine ⟨123341355308966577542716279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164455140411955436723621705 123341355308966577542716279)
        ·
          refine ⟨185012032963449866314074419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123341355308966577542716279 185012032963449866314074419)
          ·
            refine ⟨277518049445174799471111629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185012032963449866314074419 277518049445174799471111629)
            ·
              refine ⟨104069268541940549801666861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277518049445174799471111629 104069268541940549801666861)
              ·
                refine ⟨39025975703227706175625073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104069268541940549801666861 39025975703227706175625073)
                ·
                  refine ⟨29269481777420779631718805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39025975703227706175625073 29269481777420779631718805)
                  ·
                    refine ⟨1372006958316599045236819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29269481777420779631718805 1372006958316599045236819)
                    ·
                      rfl

theorem cell22_4007961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_4007961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007961 prefixEnd_4007961 := by exact prefixLift 4007961
  have htrace : WordTrace (prefixWord ++ tailWord_4007961) baseStart_4007961 baseEnd_4007961 := by
    simpa [prefixWord, tailWord_4007961, baseEnd_4007961] using wordTrace_append hprefix tailTrace_4007961
  have hstable : (prefixWord ++ tailWord_4007961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007961).length < 2 ^ (prefixWord ++ tailWord_4007961).sum := by decide
  have hdescent : baseEnd_4007961 < baseStart_4007961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007963 : List Nat := [1, 1, 1, 1, 1, 1, 3, 7, 3, 3]
def baseStart_4007963 : Nat := 118140960795 + 4007963 * 2 ^ 59
def prefixEnd_4007963 : Nat := 4983230072969 + 3 ^ 40 * 4007963 * 2
def baseEnd_4007963 : Nat := 1372007642957471706686813

theorem tailTrace_4007963 : CollatzResearch.WordTrace tailWord_4007963 prefixEnd_4007963 1372007642957471706686813 := by
  unfold tailWord_4007963
  simp only [CollatzResearch.WordTrace]
  refine ⟨146182419978842031429236543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97454946652561354286157695 146182419978842031429236543)
  ·
    refine ⟨219273629968263047143854815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146182419978842031429236543 219273629968263047143854815)
    ·
      refine ⟨328910444952394570715782223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219273629968263047143854815 328910444952394570715782223)
      ·
        refine ⟨493365667428591856073673335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328910444952394570715782223 493365667428591856073673335)
        ·
          refine ⟨740048501142887784110510003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493365667428591856073673335 740048501142887784110510003)
          ·
            refine ⟨1110072751714331676165765005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740048501142887784110510003 1110072751714331676165765005)
            ·
              refine ⟨416277281892874378562161877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1110072751714331676165765005 416277281892874378562161877)
              ·
                refine ⟨9756498794364243247550669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 416277281892874378562161877 9756498794364243247550669)
                ·
                  refine ⟨3658687047886591217831501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9756498794364243247550669 3658687047886591217831501)
                  ·
                    refine ⟨1372007642957471706686813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3658687047886591217831501 1372007642957471706686813)
                    ·
                      rfl

theorem cell22_4007963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 3].length) (baseStart_4007963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007963 prefixEnd_4007963 := by exact prefixLift 4007963
  have htrace : WordTrace (prefixWord ++ tailWord_4007963) baseStart_4007963 baseEnd_4007963 := by
    simpa [prefixWord, tailWord_4007963, baseEnd_4007963] using wordTrace_append hprefix tailTrace_4007963
  have hstable : (prefixWord ++ tailWord_4007963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007963).length < 2 ^ (prefixWord ++ tailWord_4007963).sum := by decide
  have hdescent : baseEnd_4007963 < baseStart_4007963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007969 : List Nat := [1, 2, 3, 2, 4, 2, 2, 1, 2, 3]
def baseStart_4007969 : Nat := 118140960795 + 4007969 * 2 ^ 59
def prefixEnd_4007969 : Nat := 4983230072969 + 3 ^ 40 * 4007969 * 2
def baseEnd_4007969 : Nat := 1372009696880089691036795

theorem tailTrace_4007969 : CollatzResearch.WordTrace tailWord_4007969 prefixEnd_4007969 1372009696880089691036795 := by
  unfold tailWord_4007969
  simp only [CollatzResearch.WordTrace]
  refine ⟨146182638816820294453954961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97455092544546862969303307 146182638816820294453954961)
  ·
    refine ⟨109636979112615220840466221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146182638816820294453954961 109636979112615220840466221)
    ·
      refine ⟨41113867167230707815174833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109636979112615220840466221 41113867167230707815174833)
      ·
        refine ⟨30835400375423030861381125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41113867167230707815174833 30835400375423030861381125)
        ·
          refine ⟨5781637570391818286508961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30835400375423030861381125 5781637570391818286508961)
          ·
            refine ⟨4336228177793863714881721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5781637570391818286508961 4336228177793863714881721)
            ·
              refine ⟨3252171133345397786161291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4336228177793863714881721 3252171133345397786161291)
              ·
                refine ⟨4878256700018096679241937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3252171133345397786161291 4878256700018096679241937)
                ·
                  refine ⟨3658692525013572509431453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4878256700018096679241937 3658692525013572509431453)
                  ·
                    refine ⟨1372009696880089691036795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3658692525013572509431453 1372009696880089691036795)
                    ·
                      rfl

theorem cell22_4007969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_4007969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007969 prefixEnd_4007969 := by exact prefixLift 4007969
  have htrace : WordTrace (prefixWord ++ tailWord_4007969) baseStart_4007969 baseEnd_4007969 := by
    simpa [prefixWord, tailWord_4007969, baseEnd_4007969] using wordTrace_append hprefix tailTrace_4007969
  have hstable : (prefixWord ++ tailWord_4007969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007969).length < 2 ^ (prefixWord ++ tailWord_4007969).sum := by decide
  have hdescent : baseEnd_4007969 < baseStart_4007969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007997 : List Nat := [1, 4, 1, 3, 1, 1, 2, 5, 1, 3]
def baseStart_4007997 : Nat := 118140960795 + 4007997 * 2 ^ 59
def prefixEnd_4007997 : Nat := 4983230072969 + 3 ^ 40 * 4007997 * 2
def baseEnd_4007997 : Nat := 1372019281852306951336709

theorem tailTrace_4007997 : CollatzResearch.WordTrace tailWord_4007997 prefixEnd_4007997 1372019281852306951336709 := by
  unfold tailWord_4007997
  simp only [CollatzResearch.WordTrace]
  refine ⟨146183660060718855235974245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97455773373812570157316163 146183660060718855235974245)
  ·
    refine ⟨27409436261384785356745171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146183660060718855235974245 27409436261384785356745171)
    ·
      refine ⟨41114154392077178035117757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27409436261384785356745171 41114154392077178035117757)
      ·
        refine ⟨15417807897028941763169159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41114154392077178035117757 15417807897028941763169159)
        ·
          refine ⟨23126711845543412644753739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15417807897028941763169159 23126711845543412644753739)
          ·
            refine ⟨34690067768315118967130609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23126711845543412644753739 34690067768315118967130609)
            ·
              refine ⟨26017550826236339225347957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34690067768315118967130609 26017550826236339225347957)
              ·
                refine ⟨2439145389959656802376371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26017550826236339225347957 2439145389959656802376371)
                ·
                  refine ⟨3658718084939485203564557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439145389959656802376371 3658718084939485203564557)
                  ·
                    refine ⟨1372019281852306951336709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3658718084939485203564557 1372019281852306951336709)
                    ·
                      rfl

theorem cell22_4007997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_4007997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4007997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4007997 prefixEnd_4007997 := by exact prefixLift 4007997
  have htrace : WordTrace (prefixWord ++ tailWord_4007997) baseStart_4007997 baseEnd_4007997 := by
    simpa [prefixWord, tailWord_4007997, baseEnd_4007997] using wordTrace_append hprefix tailTrace_4007997
  have hstable : (prefixWord ++ tailWord_4007997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007997).length < 2 ^ (prefixWord ++ tailWord_4007997).sum := by decide
  have hdescent : baseEnd_4007997 < baseStart_4007997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008014 : List Nat := [4, 1, 1, 1, 1, 4, 4, 2, 1, 3]
def baseStart_4008014 : Nat := 118140960795 + 4008014 * 2 ^ 59
def prefixEnd_4008014 : Nat := 4983230072969 + 3 ^ 40 * 4008014 * 2
def baseEnd_4008014 : Nat := 1372025101299724573661657

theorem tailTrace_4008014 : CollatzResearch.WordTrace tailWord_4008014 prefixEnd_4008014 1372025101299724573661657 := by
  unfold tailWord_4008014
  simp only [CollatzResearch.WordTrace]
  refine ⟨18273035012707158392417887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97456186734438178092895397 18273035012707158392417887)
  ·
    refine ⟨27409552519060737588626831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18273035012707158392417887 27409552519060737588626831)
    ·
      refine ⟨41114328778591106382940247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27409552519060737588626831 41114328778591106382940247)
      ·
        refine ⟨61671493167886659574410371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41114328778591106382940247 61671493167886659574410371)
        ·
          refine ⟨92507239751829989361615557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61671493167886659574410371 92507239751829989361615557)
          ·
            refine ⟨17345107453468123005302917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92507239751829989361615557 17345107453468123005302917)
            ·
              refine ⟨3252207647525273063494297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17345107453468123005302917 3252207647525273063494297)
              ·
                refine ⟨2439155735643954797620723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3252207647525273063494297 2439155735643954797620723)
                ·
                  refine ⟨3658733603465932196431085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439155735643954797620723 3658733603465932196431085)
                  ·
                    refine ⟨1372025101299724573661657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3658733603465932196431085 1372025101299724573661657)
                    ·
                      rfl

theorem cell22_4008014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_4008014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008014 prefixEnd_4008014 := by exact prefixLift 4008014
  have htrace : WordTrace (prefixWord ++ tailWord_4008014) baseStart_4008014 baseEnd_4008014 := by
    simpa [prefixWord, tailWord_4008014, baseEnd_4008014] using wordTrace_append hprefix tailTrace_4008014
  have hstable : (prefixWord ++ tailWord_4008014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008014).length < 2 ^ (prefixWord ++ tailWord_4008014).sum := by decide
  have hdescent : baseEnd_4008014 < baseStart_4008014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008023 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 3, 4]
def baseStart_4008023 : Nat := 118140960795 + 4008023 * 2 ^ 59
def prefixEnd_4008023 : Nat := 4983230072969 + 3 ^ 40 * 4008023 * 2
def baseEnd_4008023 : Nat := 1372028182183651550186629

theorem tailTrace_4008023 : CollatzResearch.WordTrace tailWord_4008023 prefixEnd_4008023 1372028182183651550186629 := by
  unfold tailWord_4008023
  simp only [CollatzResearch.WordTrace]
  refine ⟨146184608358624661676420723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97456405572416441117613815 146184608358624661676420723)
  ·
    refine ⟨219276912537936992514631085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146184608358624661676420723 219276912537936992514631085)
    ·
      refine ⟨82228842201726372192986657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219276912537936992514631085 82228842201726372192986657)
      ·
        refine ⟨61671631651294779144739993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82228842201726372192986657 61671631651294779144739993)
        ·
          refine ⟨46253723738471084358554995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61671631651294779144739993 46253723738471084358554995)
          ·
            refine ⟨69380585607706626537832493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46253723738471084358554995 69380585607706626537832493)
            ·
              refine ⟨26017719602889984951687185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69380585607706626537832493 26017719602889984951687185)
              ·
                refine ⟨19513289702167488713765389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26017719602889984951687185 19513289702167488713765389)
                ·
                  refine ⟨7317483638312808267662021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19513289702167488713765389 7317483638312808267662021)
                  ·
                    refine ⟨1372028182183651550186629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7317483638312808267662021 1372028182183651550186629)
                    ·
                      rfl

theorem cell22_4008023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_4008023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008023 prefixEnd_4008023 := by exact prefixLift 4008023
  have htrace : WordTrace (prefixWord ++ tailWord_4008023) baseStart_4008023 baseEnd_4008023 := by
    simpa [prefixWord, tailWord_4008023, baseEnd_4008023] using wordTrace_append hprefix tailTrace_4008023
  have hstable : (prefixWord ++ tailWord_4008023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008023).length < 2 ^ (prefixWord ++ tailWord_4008023).sum := by decide
  have hdescent : baseEnd_4008023 < baseStart_4008023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008055 : List Nat := [1, 1, 3, 1, 1, 5, 1, 5, 4]
def baseStart_4008055 : Nat := 118140960795 + 4008055 * 2 ^ 59
def prefixEnd_4008055 : Nat := 4983230072969 + 3 ^ 40 * 4008055 * 2
def baseEnd_4008055 : Nat := 457346378812538044462177

theorem tailTrace_4008055 : CollatzResearch.WordTrace tailWord_4008055 prefixEnd_4008055 457346378812538044462177 := by
  unfold tailWord_4008055
  simp only [CollatzResearch.WordTrace]
  refine ⟨146185775494508731141585619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97457183663005820761057079 146185775494508731141585619)
  ·
    refine ⟨219278663241763096712378429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146185775494508731141585619 219278663241763096712378429)
    ·
      refine ⟨82229498715661161267141911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219278663241763096712378429 82229498715661161267141911)
      ·
        refine ⟨123344248073491741900712867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82229498715661161267141911 123344248073491741900712867)
        ·
          refine ⟨185016372110237612851069301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123344248073491741900712867 185016372110237612851069301)
          ·
            refine ⟨17345284885334776204787747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185016372110237612851069301 17345284885334776204787747)
            ·
              refine ⟨26017927328002164307181621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17345284885334776204787747 26017927328002164307181621)
              ·
                refine ⟨2439180687000202903798277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26017927328002164307181621 2439180687000202903798277)
                ·
                  refine ⟨457346378812538044462177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2439180687000202903798277 457346378812538044462177)
                  ·
                    rfl

theorem cell22_4008055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 4].length) (baseStart_4008055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008055 prefixEnd_4008055 := by exact prefixLift 4008055
  have htrace : WordTrace (prefixWord ++ tailWord_4008055) baseStart_4008055 baseEnd_4008055 := by
    simpa [prefixWord, tailWord_4008055, baseEnd_4008055] using wordTrace_append hprefix tailTrace_4008055
  have hstable : (prefixWord ++ tailWord_4008055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008055).length < 2 ^ (prefixWord ++ tailWord_4008055).sum := by decide
  have hdescent : baseEnd_4008055 < baseStart_4008055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008057 : List Nat := [1, 2, 1, 3, 4, 1, 4, 1, 1, 4]
def baseStart_4008057 : Nat := 118140960795 + 4008057 * 2 ^ 59
def prefixEnd_4008057 : Nat := 4983230072969 + 3 ^ 40 * 4008057 * 2
def baseEnd_4008057 : Nat := 1372039821078486794836525

theorem tailTrace_4008057 : CollatzResearch.WordTrace tailWord_4008057 prefixEnd_4008057 1372039821078486794836525 := by
  unfold tailWord_4008057
  simp only [CollatzResearch.WordTrace]
  refine ⟨146185848440501485483158425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97457232293667656988772283 146185848440501485483158425)
  ·
    refine ⟨109639386330376114112368819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146185848440501485483158425 109639386330376114112368819)
    ·
      refine ⟨164459079495564171168553229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109639386330376114112368819 164459079495564171168553229)
      ·
        refine ⟨61672154810836564188207461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164459079495564171168553229 61672154810836564188207461)
        ·
          refine ⟨11563529027031855785288899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61672154810836564188207461 11563529027031855785288899)
          ·
            refine ⟨17345293540547783677933349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11563529027031855785288899 17345293540547783677933349)
            ·
              refine ⟨3252242538852709439612503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17345293540547783677933349 3252242538852709439612503)
              ·
                refine ⟨4878363808279064159418755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3252242538852709439612503 4878363808279064159418755)
                ·
                  refine ⟨7317545712418596239128133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4878363808279064159418755 7317545712418596239128133)
                  ·
                    refine ⟨1372039821078486794836525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7317545712418596239128133 1372039821078486794836525)
                    ·
                      rfl

theorem cell22_4008057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 1, 4].length) (baseStart_4008057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008057 prefixEnd_4008057 := by exact prefixLift 4008057
  have htrace : WordTrace (prefixWord ++ tailWord_4008057) baseStart_4008057 baseEnd_4008057 := by
    simpa [prefixWord, tailWord_4008057, baseEnd_4008057] using wordTrace_append hprefix tailTrace_4008057
  have hstable : (prefixWord ++ tailWord_4008057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008057).length < 2 ^ (prefixWord ++ tailWord_4008057).sum := by decide
  have hdescent : baseEnd_4008057 < baseStart_4008057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008072 : List Nat := [2, 1, 3, 4, 1, 1, 2, 4, 4]
def baseStart_4008072 : Nat := 118140960795 + 4008072 * 2 ^ 59
def prefixEnd_4008072 : Nat := 4983230072969 + 3 ^ 40 * 4008072 * 2
def baseEnd_4008072 : Nat := 457348318628343918570493

theorem tailTrace_4008072 : CollatzResearch.WordTrace tailWord_4008072 prefixEnd_4008072 457348318628343918570493 := by
  unfold tailWord_4008072
  simp only [CollatzResearch.WordTrace]
  refine ⟨73093197767723571522477235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97457597023631428696636313 73093197767723571522477235)
  ·
    refine ⟨109639796651585357283715853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73093197767723571522477235 109639796651585357283715853)
    ·
      refine ⟨41114923744344508981393445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109639796651585357283715853 41114923744344508981393445)
      ·
        refine ⟨7709048202064595434011271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41114923744344508981393445 7709048202064595434011271)
        ·
          refine ⟨11563572303096893151016907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7709048202064595434011271 11563572303096893151016907)
          ·
            refine ⟨17345358454645339726525361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11563572303096893151016907 17345358454645339726525361)
            ·
              refine ⟨13009018840984004794894021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17345358454645339726525361 13009018840984004794894021)
              ·
                refine ⟨2439191032684500899042629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13009018840984004794894021 2439191032684500899042629)
                ·
                  refine ⟨457348318628343918570493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2439191032684500899042629 457348318628343918570493)
                  ·
                    rfl

theorem cell22_4008072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 4].length) (baseStart_4008072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008072 prefixEnd_4008072 := by exact prefixLift 4008072
  have htrace : WordTrace (prefixWord ++ tailWord_4008072) baseStart_4008072 baseEnd_4008072 := by
    simpa [prefixWord, tailWord_4008072, baseEnd_4008072] using wordTrace_append hprefix tailTrace_4008072
  have hstable : (prefixWord ++ tailWord_4008072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008072).length < 2 ^ (prefixWord ++ tailWord_4008072).sum := by decide
  have hdescent : baseEnd_4008072 < baseStart_4008072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008087 : List Nat := [1, 1, 3, 3, 4, 2, 1, 1, 1, 5]
def baseStart_4008087 : Nat := 118140960795 + 4008087 * 2 ^ 59
def prefixEnd_4008087 : Nat := 4983230072969 + 3 ^ 40 * 4008087 * 2
def baseEnd_4008087 : Nat := 1372050090691576716586433

theorem tailTrace_4008087 : CollatzResearch.WordTrace tailWord_4008087 prefixEnd_4008087 1372050090691576716586433 := by
  unfold tailWord_4008087
  simp only [CollatzResearch.WordTrace]
  refine ⟨146186942630392800606750515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97457961753595200404500343 146186942630392800606750515)
  ·
    refine ⟨219280413945589200910125773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146186942630392800606750515 219280413945589200910125773)
    ·
      refine ⟨82230155229595950341297165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219280413945589200910125773 82230155229595950341297165)
      ·
        refine ⟨30836308211098481377986437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82230155229595950341297165 30836308211098481377986437)
        ·
          refine ⟨5781807789580965258372457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30836308211098481377986437 5781807789580965258372457)
          ·
            refine ⟨4336355842185723943779343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5781807789580965258372457 4336355842185723943779343)
            ·
              refine ⟨6504533763278585915669015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4336355842185723943779343 6504533763278585915669015)
              ·
                refine ⟨9756800644917878873503523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6504533763278585915669015 9756800644917878873503523)
                ·
                  refine ⟨14635200967376818310255285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9756800644917878873503523 14635200967376818310255285)
                  ·
                    refine ⟨1372050090691576716586433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14635200967376818310255285 1372050090691576716586433)
                    ·
                      rfl

theorem cell22_4008087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_4008087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008087 prefixEnd_4008087 := by exact prefixLift 4008087
  have htrace : WordTrace (prefixWord ++ tailWord_4008087) baseStart_4008087 baseEnd_4008087 := by
    simpa [prefixWord, tailWord_4008087, baseEnd_4008087] using wordTrace_append hprefix tailTrace_4008087
  have hstable : (prefixWord ++ tailWord_4008087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008087).length < 2 ^ (prefixWord ++ tailWord_4008087).sum := by decide
  have hdescent : baseEnd_4008087 < baseStart_4008087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008100 : List Nat := [2, 3, 1, 2, 4, 1, 1, 8]
def baseStart_4008100 : Nat := 118140960795 + 4008100 * 2 ^ 59
def prefixEnd_4008100 : Nat := 4983230072969 + 3 ^ 40 * 4008100 * 2
def baseEnd_4008100 : Nat := 152450504539694335112377

theorem tailTrace_4008100 : CollatzResearch.WordTrace tailWord_4008100 prefixEnd_4008100 152450504539694335112377 := by
  unfold tailWord_4008100
  simp only [CollatzResearch.WordTrace]
  refine ⟨73093708389672851913486877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97458277852897135884649169 73093708389672851913486877)
  ·
    refine ⟨27410140646127319467557579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73093708389672851913486877 27410140646127319467557579)
    ·
      refine ⟨41115210969190979201336369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27410140646127319467557579 41115210969190979201336369)
      ·
        refine ⟨30836408226893234401002277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41115210969190979201336369 30836408226893234401002277)
        ·
          refine ⟨5781826542542481450187927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30836408226893234401002277 5781826542542481450187927)
          ·
            refine ⟨8672739813813722175281891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5781826542542481450187927 8672739813813722175281891)
            ·
              refine ⟨13009109720720583262922837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8672739813813722175281891 13009109720720583262922837)
              ·
                refine ⟨152450504539694335112377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13009109720720583262922837 152450504539694335112377)
                ·
                  rfl

theorem cell22_4008100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 8].length) (baseStart_4008100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008100 prefixEnd_4008100 := by exact prefixLift 4008100
  have htrace : WordTrace (prefixWord ++ tailWord_4008100) baseStart_4008100 baseEnd_4008100 := by
    simpa [prefixWord, tailWord_4008100, baseEnd_4008100] using wordTrace_append hprefix tailTrace_4008100
  have hstable : (prefixWord ++ tailWord_4008100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008100).length < 2 ^ (prefixWord ++ tailWord_4008100).sum := by decide
  have hdescent : baseEnd_4008100 < baseStart_4008100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008106 : List Nat := [3, 1, 5, 1, 2, 2, 1, 3, 4]
def baseStart_4008106 : Nat := 118140960795 + 4008106 * 2 ^ 59
def prefixEnd_4008106 : Nat := 4983230072969 + 3 ^ 40 * 4008106 * 2
def baseEnd_4008106 : Nat := 457352198259955666787125

theorem tailTrace_4008106 : CollatzResearch.WordTrace tailWord_4008106 prefixEnd_4008106 457352198259955666787125 := by
  unfold tailWord_4008106
  simp only [CollatzResearch.WordTrace]
  refine ⟨36546908904330991712923043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97458423744882644567794781 36546908904330991712923043)
  ·
    refine ⟨54820363356496487569384565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36546908904330991712923043 54820363356496487569384565)
    ·
      refine ⟨5139409064671545709629803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54820363356496487569384565 5139409064671545709629803)
      ·
        refine ⟨7709113597007318564444705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5139409064671545709629803 7709113597007318564444705)
        ·
          refine ⟨5781835197755488923333529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7709113597007318564444705 5781835197755488923333529)
          ·
            refine ⟨4336376398316616692500147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5781835197755488923333529 4336376398316616692500147)
            ·
              refine ⟨6504564597474925038750221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4336376398316616692500147 6504564597474925038750221)
              ·
                refine ⟨2439211724053096889531333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6504564597474925038750221 2439211724053096889531333)
                ·
                  refine ⟨457352198259955666787125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2439211724053096889531333 457352198259955666787125)
                  ·
                    rfl

theorem cell22_4008106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_4008106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008106 prefixEnd_4008106 := by exact prefixLift 4008106
  have htrace : WordTrace (prefixWord ++ tailWord_4008106) baseStart_4008106 baseEnd_4008106 := by
    simpa [prefixWord, tailWord_4008106, baseEnd_4008106] using wordTrace_append hprefix tailTrace_4008106
  have hstable : (prefixWord ++ tailWord_4008106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008106).length < 2 ^ (prefixWord ++ tailWord_4008106).sum := by decide
  have hdescent : baseEnd_4008106 < baseStart_4008106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008117 : List Nat := [1, 3, 3, 4, 1, 2, 8]
def baseStart_4008117 : Nat := 118140960795 + 4008117 * 2 ^ 59
def prefixEnd_4008117 : Nat := 4983230072969 + 3 ^ 40 * 4008117 * 2
def baseEnd_4008117 : Nat := 50817050381654319938383

theorem tailTrace_4008117 : CollatzResearch.WordTrace tailWord_4008117 prefixEnd_4008117 50817050381654319938383 := by
  unfold tailWord_4008117
  simp only [CollatzResearch.WordTrace]
  refine ⟨146188036820284115730342605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97458691213522743820228403 146188036820284115730342605)
  ·
    refine ⟨54820513807606543398878477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146188036820284115730342605 54820513807606543398878477)
    ·
      refine ⟨20557692677852453774579429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54820513807606543398878477 20557692677852453774579429)
      ·
        refine ⟨3854567377097335082733643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20557692677852453774579429 3854567377097335082733643)
        ·
          refine ⟨5781851065646002624100465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3854567377097335082733643 5781851065646002624100465)
          ·
            refine ⟨4336388299234501968075349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5781851065646002624100465 4336388299234501968075349)
            ·
              refine ⟨50817050381654319938383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4336388299234501968075349 50817050381654319938383)
              ·
                rfl

theorem cell22_4008117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 8].length) (baseStart_4008117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008117 prefixEnd_4008117 := by exact prefixLift 4008117
  have htrace : WordTrace (prefixWord ++ tailWord_4008117) baseStart_4008117 baseEnd_4008117 := by
    simpa [prefixWord, tailWord_4008117, baseEnd_4008117] using wordTrace_append hprefix tailTrace_4008117
  have hstable : (prefixWord ++ tailWord_4008117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008117).length < 2 ^ (prefixWord ++ tailWord_4008117).sum := by decide
  have hdescent : baseEnd_4008117 < baseStart_4008117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008143 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 1, 7]
def baseStart_4008143 : Nat := 118140960795 + 4008143 * 2 ^ 59
def prefixEnd_4008143 : Nat := 4983230072969 + 3 ^ 40 * 4008143 * 2
def baseEnd_4008143 : Nat := 1372069260636011237186261

theorem tailTrace_4008143 : CollatzResearch.WordTrace tailWord_4008143 prefixEnd_4008143 1372069260636011237186261 := by
  unfold tailWord_4008143
  simp only [CollatzResearch.WordTrace]
  refine ⟨146188985118189922170789083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97459323412126614780526055 146188985118189922170789083)
  ·
    refine ⟨219283477677284883256183625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146188985118189922170789083 219283477677284883256183625)
    ·
      refine ⟨164462608257963662442137719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219283477677284883256183625 164462608257963662442137719)
      ·
        refine ⟨246693912386945493663206579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164462608257963662442137719 246693912386945493663206579)
        ·
          refine ⟨370040868580418240494809869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246693912386945493663206579 370040868580418240494809869)
          ·
            refine ⟨138765325717656840185553701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370040868580418240494809869 138765325717656840185553701)
            ·
              refine ⟨26018498572060657534791319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138765325717656840185553701 26018498572060657534791319)
              ·
                refine ⟨39027747858090986302186979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26018498572060657534791319 39027747858090986302186979)
                ·
                  refine ⟨58541621787136479453280469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39027747858090986302186979 58541621787136479453280469)
                  ·
                    refine ⟨1372069260636011237186261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58541621787136479453280469 1372069260636011237186261)
                    ·
                      rfl

theorem cell22_4008143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_4008143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008143 prefixEnd_4008143 := by exact prefixLift 4008143
  have htrace : WordTrace (prefixWord ++ tailWord_4008143) baseStart_4008143 baseEnd_4008143 := by
    simpa [prefixWord, tailWord_4008143, baseEnd_4008143] using wordTrace_append hprefix tailTrace_4008143
  have hstable : (prefixWord ++ tailWord_4008143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008143).length < 2 ^ (prefixWord ++ tailWord_4008143).sum := by decide
  have hdescent : baseEnd_4008143 < baseStart_4008143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008224 : List Nat := [2, 1, 1, 5, 2, 2, 2, 3, 4]
def baseStart_4008224 : Nat := 118140960795 + 4008224 * 2 ^ 59
def prefixEnd_4008224 : Nat := 4983230072969 + 3 ^ 40 * 4008224 * 2
def baseEnd_4008224 : Nat := 457365662863784675303671

theorem tailTrace_4008224 : CollatzResearch.WordTrace tailWord_4008224 prefixEnd_4008224 457365662863784675303671 := by
  unfold tailWord_4008224
  simp only [CollatzResearch.WordTrace]
  refine ⟨73095969715448236502243863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97461292953930982002991817 73095969715448236502243863)
  ·
    refine ⟨109643954573172354753365795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73095969715448236502243863 109643954573172354753365795)
    ·
      refine ⟨164465931859758532130048693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109643954573172354753365795 164465931859758532130048693)
      ·
        refine ⟨15418681111852362387192065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164465931859758532130048693 15418681111852362387192065)
        ·
          refine ⟨11564010833889271790394049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15418681111852362387192065 11564010833889271790394049)
          ·
            refine ⟨8673008125416953842795537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11564010833889271790394049 8673008125416953842795537)
            ·
              refine ⟨6504756094062715382096653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8673008125416953842795537 6504756094062715382096653)
              ·
                refine ⟨2439283535273518268286245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6504756094062715382096653 2439283535273518268286245)
                ·
                  refine ⟨457365662863784675303671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2439283535273518268286245 457365662863784675303671)
                  ·
                    rfl

theorem cell22_4008224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 4].length) (baseStart_4008224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008224 prefixEnd_4008224 := by exact prefixLift 4008224
  have htrace : WordTrace (prefixWord ++ tailWord_4008224) baseStart_4008224 baseEnd_4008224 := by
    simpa [prefixWord, tailWord_4008224, baseEnd_4008224] using wordTrace_append hprefix tailTrace_4008224
  have hstable : (prefixWord ++ tailWord_4008224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008224).length < 2 ^ (prefixWord ++ tailWord_4008224).sum := by decide
  have hdescent : baseEnd_4008224 < baseStart_4008224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008226 : List Nat := [3, 3, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_4008226 : Nat := 118140960795 + 4008226 * 2 ^ 59
def prefixEnd_4008226 : Nat := 4983230072969 + 3 ^ 40 * 4008226 * 2
def baseEnd_4008226 : Nat := 1372097673232226687361007

theorem tailTrace_4008226 : CollatzResearch.WordTrace tailWord_4008226 prefixEnd_4008226 1372097673232226687361007 := by
  unfold tailWord_4008226
  simp only [CollatzResearch.WordTrace]
  refine ⟨36548003094222306836515133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97461341584592818230707021 36548003094222306836515133)
  ·
    refine ⟨13705501160333365063693175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36548003094222306836515133 13705501160333365063693175)
    ·
      refine ⟨20558251740500047595539763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13705501160333365063693175 20558251740500047595539763)
      ·
        refine ⟨30837377610750071393309645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20558251740500047595539763 30837377610750071393309645)
        ·
          refine ⟨11564016604031276772491117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30837377610750071393309645 11564016604031276772491117)
          ·
            refine ⟨4336506226511728789684169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11564016604031276772491117 4336506226511728789684169)
            ·
              refine ⟨3252379669883796592263127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4336506226511728789684169 3252379669883796592263127)
              ·
                refine ⟨4878569504825694888394691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3252379669883796592263127 4878569504825694888394691)
                ·
                  refine ⟨7317854257238542332592037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4878569504825694888394691 7317854257238542332592037)
                  ·
                    refine ⟨1372097673232226687361007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7317854257238542332592037 1372097673232226687361007)
                    ·
                      rfl

theorem cell22_4008226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_4008226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008226 prefixEnd_4008226 := by exact prefixLift 4008226
  have htrace : WordTrace (prefixWord ++ tailWord_4008226) baseStart_4008226 baseEnd_4008226 := by
    simpa [prefixWord, tailWord_4008226, baseEnd_4008226] using wordTrace_append hprefix tailTrace_4008226
  have hstable : (prefixWord ++ tailWord_4008226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008226).length < 2 ^ (prefixWord ++ tailWord_4008226).sum := by decide
  have hdescent : baseEnd_4008226 < baseStart_4008226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008325 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 8]
def baseStart_4008325 : Nat := 118140960795 + 4008325 * 2 ^ 59
def prefixEnd_4008325 : Nat := 4983230072969 + 3 ^ 40 * 4008325 * 2
def baseEnd_4008325 : Nat := 457377187651807809711901

theorem tailTrace_4008325 : CollatzResearch.WordTrace tailWord_4008325 prefixEnd_4008325 457377187651807809711901 := by
  unfold tailWord_4008325
  simp only [CollatzResearch.WordTrace]
  refine ⟨146195623203530567253914429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97463748802353711502609619 146195623203530567253914429)
  ·
    refine ⟨54823358701323962720217911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146195623203530567253914429 54823358701323962720217911)
    ·
      refine ⟨82235038051985944080326867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54823358701323962720217911 82235038051985944080326867)
      ·
        refine ⟨123352557077978916120490301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82235038051985944080326867 123352557077978916120490301)
        ·
          refine ⟨46257208904242093545183863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123352557077978916120490301 46257208904242093545183863)
          ·
            refine ⟨69385813356363140317775795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46257208904242093545183863 69385813356363140317775795)
            ·
              refine ⟨104078720034544710476663693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69385813356363140317775795 104078720034544710476663693)
              ·
                refine ⟨39029520012954266428748885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104078720034544710476663693 39029520012954266428748885)
                ·
                  refine ⟨457377187651807809711901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39029520012954266428748885 457377187651807809711901)
                  ·
                    rfl

theorem cell22_4008325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_4008325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008325 prefixEnd_4008325 := by exact prefixLift 4008325
  have htrace : WordTrace (prefixWord ++ tailWord_4008325) baseStart_4008325 baseEnd_4008325 := by
    simpa [prefixWord, tailWord_4008325, baseEnd_4008325] using wordTrace_append hprefix tailTrace_4008325
  have hstable : (prefixWord ++ tailWord_4008325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008325).length < 2 ^ (prefixWord ++ tailWord_4008325).sum := by decide
  have hdescent : baseEnd_4008325 < baseStart_4008325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008327 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 3, 4]
def baseStart_4008327 : Nat := 118140960795 + 4008327 * 2 ^ 59
def prefixEnd_4008327 : Nat := 4983230072969 + 3 ^ 40 * 4008327 * 2
def baseEnd_4008327 : Nat := 1372132247596296090585697

theorem tailTrace_4008327 : CollatzResearch.WordTrace tailWord_4008327 prefixEnd_4008327 1372132247596296090585697 := by
  unfold tailWord_4008327
  simp only [CollatzResearch.WordTrace]
  refine ⟨146195696149523321595487235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97463797433015547730324823 146195696149523321595487235)
  ·
    refine ⟨219293544224284982393230853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146195696149523321595487235 219293544224284982393230853)
    ·
      refine ⟨41117539542053434198730785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219293544224284982393230853 41117539542053434198730785)
      ·
        refine ⟨30838154656540075649048089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41117539542053434198730785 30838154656540075649048089)
        ·
          refine ⟨23128615992405056736786067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30838154656540075649048089 23128615992405056736786067)
          ·
            refine ⟨34692923988607585105179101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23128615992405056736786067 34692923988607585105179101)
            ·
              refine ⟨13009846495727844414442163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34692923988607585105179101 13009846495727844414442163)
              ·
                refine ⟨19514769743591766621663245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13009846495727844414442163 19514769743591766621663245)
                ·
                  refine ⟨7318038653846912483123717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19514769743591766621663245 7318038653846912483123717)
                  ·
                    refine ⟨1372132247596296090585697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7318038653846912483123717 1372132247596296090585697)
                    ·
                      rfl

theorem cell22_4008327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_4008327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008327 prefixEnd_4008327 := by exact prefixLift 4008327
  have htrace : WordTrace (prefixWord ++ tailWord_4008327) baseStart_4008327 baseEnd_4008327 := by
    simpa [prefixWord, tailWord_4008327, baseEnd_4008327] using wordTrace_append hprefix tailTrace_4008327
  have hstable : (prefixWord ++ tailWord_4008327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008327).length < 2 ^ (prefixWord ++ tailWord_4008327).sum := by decide
  have hdescent : baseEnd_4008327 < baseStart_4008327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008492 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 5, 5]
def baseStart_4008492 : Nat := 118140960795 + 4008492 * 2 ^ 59
def prefixEnd_4008492 : Nat := 4983230072969 + 3 ^ 40 * 4008492 * 2
def baseEnd_4008492 : Nat := 1372188730468290660210191

theorem tailTrace_4008492 : CollatzResearch.WordTrace tailWord_4008492 prefixEnd_4008492 1372188730468290660210191 := by
  unfold tailWord_4008492
  simp only [CollatzResearch.WordTrace]
  refine ⟨73100857096962777387621865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97467809462617036516829153 73100857096962777387621865)
  ·
    refine ⟨54825642822722083040716399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73100857096962777387621865 54825642822722083040716399)
    ·
      refine ⟨82238464234083124561074599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54825642822722083040716399 82238464234083124561074599)
      ·
        refine ⟨123357696351124686841611899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82238464234083124561074599 123357696351124686841611899)
        ·
          refine ⟨185036544526687030262417849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123357696351124686841611899 185036544526687030262417849)
          ·
            refine ⟨138777408395015272696813387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185036544526687030262417849 138777408395015272696813387)
            ·
              refine ⟨208166112592522909045220081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138777408395015272696813387 208166112592522909045220081)
              ·
                refine ⟨156124584444392181783915061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208166112592522909045220081 156124584444392181783915061)
                ·
                  refine ⟨14636679791661767042242037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156124584444392181783915061 14636679791661767042242037)
                  ·
                    refine ⟨1372188730468290660210191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14636679791661767042242037 1372188730468290660210191)
                    ·
                      rfl

theorem cell22_4008492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_4008492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008492 prefixEnd_4008492 := by exact prefixLift 4008492
  have htrace : WordTrace (prefixWord ++ tailWord_4008492) baseStart_4008492 baseEnd_4008492 := by
    simpa [prefixWord, tailWord_4008492, baseEnd_4008492] using wordTrace_append hprefix tailTrace_4008492
  have hstable : (prefixWord ++ tailWord_4008492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008492).length < 2 ^ (prefixWord ++ tailWord_4008492).sum := by decide
  have hdescent : baseEnd_4008492 < baseStart_4008492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008509 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_4008509 : Nat := 118140960795 + 4008509 * 2 ^ 59
def prefixEnd_4008509 : Nat := 4983230072969 + 3 ^ 40 * 4008509 * 2
def baseEnd_4008509 : Nat := 1372194549915708282535139

theorem tailTrace_4008509 : CollatzResearch.WordTrace tailWord_4008509 prefixEnd_4008509 1372194549915708282535139 := by
  unfold tailWord_4008509
  simp only [CollatzResearch.WordTrace]
  refine ⟨146202334234863966678612581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97468222823242644452408387 146202334234863966678612581)
  ·
    refine ⟨27412937669036993752239859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146202334234863966678612581 27412937669036993752239859)
    ·
      refine ⟨41119406503555490628359789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27412937669036993752239859 41119406503555490628359789)
      ·
        refine ⟨15419777438833308985634921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41119406503555490628359789 15419777438833308985634921)
        ·
          refine ⟨11564833079124981739226191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15419777438833308985634921 11564833079124981739226191)
          ·
            refine ⟨17347249618687472608839287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11564833079124981739226191 17347249618687472608839287)
            ·
              refine ⟨26020874428031208913258931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17347249618687472608839287 26020874428031208913258931)
              ·
                refine ⟨39031311642046813369888397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26020874428031208913258931 39031311642046813369888397)
                ·
                  refine ⟨14636741865767555013708149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39031311642046813369888397 14636741865767555013708149)
                  ·
                    refine ⟨1372194549915708282535139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14636741865767555013708149 1372194549915708282535139)
                    ·
                      rfl

theorem cell22_4008509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_4008509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008509 prefixEnd_4008509 := by exact prefixLift 4008509
  have htrace : WordTrace (prefixWord ++ tailWord_4008509) baseStart_4008509 baseEnd_4008509 := by
    simpa [prefixWord, tailWord_4008509, baseEnd_4008509] using wordTrace_append hprefix tailTrace_4008509
  have hstable : (prefixWord ++ tailWord_4008509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008509).length < 2 ^ (prefixWord ++ tailWord_4008509).sum := by decide
  have hdescent : baseEnd_4008509 < baseStart_4008509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008513 : List Nat := [1, 2, 5, 1, 1, 3, 3, 1, 1, 4]
def baseStart_4008513 : Nat := 118140960795 + 4008513 * 2 ^ 59
def prefixEnd_4008513 : Nat := 4983230072969 + 3 ^ 40 * 4008513 * 2
def baseEnd_4008513 : Nat := 1372195919197453605435127

theorem tailTrace_4008513 : CollatzResearch.WordTrace tailWord_4008513 prefixEnd_4008513 1372195919197453605435127 := by
  unfold tailWord_4008513
  simp only [CollatzResearch.WordTrace]
  refine ⟨146202480126849475361758193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97468320084566316907838795 146202480126849475361758193)
  ·
    refine ⟨109651860095137106521318645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146202480126849475361758193 109651860095137106521318645)
    ·
      refine ⟨10279861883919103736373623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109651860095137106521318645 10279861883919103736373623)
      ·
        refine ⟨15419792825878655604560435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10279861883919103736373623 15419792825878655604560435)
        ·
          refine ⟨23129689238817983406840653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15419792825878655604560435 23129689238817983406840653)
          ·
            refine ⟨8673633464556743777565245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23129689238817983406840653 8673633464556743777565245)
            ·
              refine ⟨3252612549208778916586967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8673633464556743777565245 3252612549208778916586967)
              ·
                refine ⟨4878918823813168374880451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3252612549208778916586967 4878918823813168374880451)
                ·
                  refine ⟨7318378235719752562320677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4878918823813168374880451 7318378235719752562320677)
                  ·
                    refine ⟨1372195919197453605435127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7318378235719752562320677 1372195919197453605435127)
                    ·
                      rfl

theorem cell22_4008513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_4008513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008513 prefixEnd_4008513 := by exact prefixLift 4008513
  have htrace : WordTrace (prefixWord ++ tailWord_4008513) baseStart_4008513 baseEnd_4008513 := by
    simpa [prefixWord, tailWord_4008513, baseEnd_4008513] using wordTrace_append hprefix tailTrace_4008513
  have hstable : (prefixWord ++ tailWord_4008513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008513).length < 2 ^ (prefixWord ++ tailWord_4008513).sum := by decide
  have hdescent : baseEnd_4008513 < baseStart_4008513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008522 : List Nat := [3, 1, 2, 1, 1, 14]
def baseStart_4008522 : Nat := 118140960795 + 4008522 * 2 ^ 59
def prefixEnd_4008522 : Nat := 4983230072969 + 3 ^ 40 * 4008522 * 2
def baseEnd_4008522 : Nat := 16940728396066426937779

theorem tailTrace_4008522 : CollatzResearch.WordTrace tailWord_4008522 prefixEnd_4008522 16940728396066426937779 := by
  unfold tailWord_4008522
  simp only [CollatzResearch.WordTrace]
  refine ⟨36550702095954217474708955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97468538922544579932557213 36550702095954217474708955)
  ·
    refine ⟨54826053143931326212063433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36550702095954217474708955 54826053143931326212063433)
    ·
      refine ⟨41119539857948494659047575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54826053143931326212063433 41119539857948494659047575)
      ·
        refine ⟨61679309786922741988571363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41119539857948494659047575 61679309786922741988571363)
        ·
          refine ⟨92518964680384112982857045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61679309786922741988571363 92518964680384112982857045)
          ·
            refine ⟨16940728396066426937779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 92518964680384112982857045 16940728396066426937779)
            ·
              rfl

theorem cell22_4008522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 14].length) (baseStart_4008522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008522 prefixEnd_4008522 := by exact prefixLift 4008522
  have htrace : WordTrace (prefixWord ++ tailWord_4008522) baseStart_4008522 baseEnd_4008522 := by
    simpa [prefixWord, tailWord_4008522, baseEnd_4008522] using wordTrace_append hprefix tailTrace_4008522
  have hstable : (prefixWord ++ tailWord_4008522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008522).length < 2 ^ (prefixWord ++ tailWord_4008522).sum := by decide
  have hdescent : baseEnd_4008522 < baseStart_4008522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008524 : List Nat := [2, 2, 1, 3, 1, 2, 1, 4, 2, 4]
def baseStart_4008524 : Nat := 118140960795 + 4008524 * 2 ^ 59
def prefixEnd_4008524 : Nat := 4983230072969 + 3 ^ 40 * 4008524 * 2
def baseEnd_4008524 : Nat := 1372199684722253243410093

theorem tailTrace_4008524 : CollatzResearch.WordTrace tailWord_4008524 prefixEnd_4008524 1372199684722253243410093 := by
  unfold tailWord_4008524
  simp only [CollatzResearch.WordTrace]
  refine ⟨73101440664904812120204313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97468587553206416160272417 73101440664904812120204313)
  ·
    refine ⟨54826080498678609090153235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73101440664904812120204313 54826080498678609090153235)
    ·
      refine ⟨82239120748017913635229853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54826080498678609090153235 82239120748017913635229853)
      ·
        refine ⟨30839670280506717613211195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82239120748017913635229853 30839670280506717613211195)
        ·
          refine ⟨46259505420760076419816793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30839670280506717613211195 46259505420760076419816793)
          ·
            refine ⟨34694629065570057314862595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46259505420760076419816793 34694629065570057314862595)
            ·
              refine ⟨52041943598355085972293893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34694629065570057314862595 52041943598355085972293893)
              ·
                refine ⟨9757864424691578619805105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52041943598355085972293893 9757864424691578619805105)
                ·
                  refine ⟨7318398318518683964853829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9757864424691578619805105 7318398318518683964853829)
                  ·
                    refine ⟨1372199684722253243410093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7318398318518683964853829 1372199684722253243410093)
                    ·
                      rfl

theorem cell22_4008524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_4008524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008524 prefixEnd_4008524 := by exact prefixLift 4008524
  have htrace : WordTrace (prefixWord ++ tailWord_4008524) baseStart_4008524 baseEnd_4008524 := by
    simpa [prefixWord, tailWord_4008524, baseEnd_4008524] using wordTrace_append hprefix tailTrace_4008524
  have hstable : (prefixWord ++ tailWord_4008524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008524).length < 2 ^ (prefixWord ++ tailWord_4008524).sum := by decide
  have hdescent : baseEnd_4008524 < baseStart_4008524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008526 : List Nat := [4, 1, 1, 1, 1, 2, 3, 4, 2, 3]
def baseStart_4008526 : Nat := 118140960795 + 4008526 * 2 ^ 59
def prefixEnd_4008526 : Nat := 4983230072969 + 3 ^ 40 * 4008526 * 2
def baseEnd_4008526 : Nat := 1372200369363125904860087

theorem tailTrace_4008526 : CollatzResearch.WordTrace tailWord_4008526 prefixEnd_4008526 1372200369363125904860087 := by
  unfold tailWord_4008526
  simp only [CollatzResearch.WordTrace]
  refine ⟨18275369284475297322747679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97468636183868252387987621 18275369284475297322747679)
  ·
    refine ⟨27413053926712945984121519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18275369284475297322747679 27413053926712945984121519)
    ·
      refine ⟨41119580890069418976182279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27413053926712945984121519 41119580890069418976182279)
      ·
        refine ⟨61679371335104128464273419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41119580890069418976182279 61679371335104128464273419)
        ·
          refine ⟨92519057002656192696410129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61679371335104128464273419 92519057002656192696410129)
          ·
            refine ⟨69389292751992144522307597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92519057002656192696410129 69389292751992144522307597)
            ·
              refine ⟨26020984781997054195865349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69389292751992144522307597 26020984781997054195865349)
              ·
                refine ⟨4878934646624447661724753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26020984781997054195865349 4878934646624447661724753)
                ·
                  refine ⟨3659200984968335746293565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4878934646624447661724753 3659200984968335746293565)
                  ·
                    refine ⟨1372200369363125904860087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3659200984968335746293565 1372200369363125904860087)
                    ·
                      rfl

theorem cell22_4008526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_4008526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008526 prefixEnd_4008526 := by exact prefixLift 4008526
  have htrace : WordTrace (prefixWord ++ tailWord_4008526) baseStart_4008526 baseEnd_4008526 := by
    simpa [prefixWord, tailWord_4008526, baseEnd_4008526] using wordTrace_append hprefix tailTrace_4008526
  have hstable : (prefixWord ++ tailWord_4008526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008526).length < 2 ^ (prefixWord ++ tailWord_4008526).sum := by decide
  have hdescent : baseEnd_4008526 < baseStart_4008526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008537 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 4, 7]
def baseStart_4008537 : Nat := 118140960795 + 4008537 * 2 ^ 59
def prefixEnd_4008537 : Nat := 4983230072969 + 3 ^ 40 * 4008537 * 2
def baseEnd_4008537 : Nat := 1372204134887925542835053

theorem tailTrace_4008537 : CollatzResearch.WordTrace tailWord_4008537 prefixEnd_4008537 1372204134887925542835053 := by
  unfold tailWord_4008537
  simp only [CollatzResearch.WordTrace]
  refine ⟨146203355478762527460631865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97468903652508351640421243 146203355478762527460631865)
  ·
    refine ⟨109652516609071895595473899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146203355478762527460631865 109652516609071895595473899)
    ·
      refine ⟨164478774913607843393210849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109652516609071895595473899 164478774913607843393210849)
      ·
        refine ⟨123359081185205882544908137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164478774913607843393210849 123359081185205882544908137)
        ·
          refine ⟨92519310888904411908681103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123359081185205882544908137 92519310888904411908681103)
          ·
            refine ⟨138778966333356617863021655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92519310888904411908681103 138778966333356617863021655)
            ·
              refine ⟨208168449500034926794532483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138778966333356617863021655 208168449500034926794532483)
              ·
                refine ⟨312252674250052390191798725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208168449500034926794532483 312252674250052390191798725)
                ·
                  refine ⟨58547376421884823160962261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 312252674250052390191798725 58547376421884823160962261)
                  ·
                    refine ⟨1372204134887925542835053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58547376421884823160962261 1372204134887925542835053)
                    ·
                      rfl

theorem cell22_4008537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_4008537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008537 prefixEnd_4008537 := by exact prefixLift 4008537
  have htrace : WordTrace (prefixWord ++ tailWord_4008537) baseStart_4008537 baseEnd_4008537 := by
    simpa [prefixWord, tailWord_4008537, baseEnd_4008537] using wordTrace_append hprefix tailTrace_4008537
  have hstable : (prefixWord ++ tailWord_4008537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008537).length < 2 ^ (prefixWord ++ tailWord_4008537).sum := by decide
  have hdescent : baseEnd_4008537 < baseStart_4008537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008558 : List Nat := [4, 1, 2, 2, 2, 3, 1, 1, 2, 4]
def baseStart_4008558 : Nat := 118140960795 + 4008558 * 2 ^ 59
def prefixEnd_4008558 : Nat := 4983230072969 + 3 ^ 40 * 4008558 * 2
def baseEnd_4008558 : Nat := 1372211323617088488059989

theorem tailTrace_4008558 : CollatzResearch.WordTrace tailWord_4008558 prefixEnd_4008558 1372211323617088488059989 := by
  unfold tailWord_4008558
  simp only [CollatzResearch.WordTrace]
  refine ⟨18275515176460806005893291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97469414274457632031430885 18275515176460806005893291)
  ·
    refine ⟨27413272764691209008839937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18275515176460806005893291 27413272764691209008839937)
    ·
      refine ⟨20559954573518406756629953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27413272764691209008839937 20559954573518406756629953)
      ·
        refine ⟨15419965930138805067472465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20559954573518406756629953 15419965930138805067472465)
        ·
          refine ⟨11564974447604103800604349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15419965930138805067472465 11564974447604103800604349)
          ·
            refine ⟨4336865417851538925226631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11564974447604103800604349 4336865417851538925226631)
            ·
              refine ⟨6505298126777308387839947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4336865417851538925226631 6505298126777308387839947)
              ·
                refine ⟨9757947190165962581759921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6505298126777308387839947 9757947190165962581759921)
                ·
                  refine ⟨7318460392624471936319941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9757947190165962581759921 7318460392624471936319941)
                  ·
                    refine ⟨1372211323617088488059989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7318460392624471936319941 1372211323617088488059989)
                    ·
                      rfl

theorem cell22_4008558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_4008558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008558 prefixEnd_4008558 := by exact prefixLift 4008558
  have htrace : WordTrace (prefixWord ++ tailWord_4008558) baseStart_4008558 baseEnd_4008558 := by
    simpa [prefixWord, tailWord_4008558, baseEnd_4008558] using wordTrace_append hprefix tailTrace_4008558
  have hstable : (prefixWord ++ tailWord_4008558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008558).length < 2 ^ (prefixWord ++ tailWord_4008558).sum := by decide
  have hdescent : baseEnd_4008558 < baseStart_4008558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008599 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 2, 5]
def baseStart_4008599 : Nat := 118140960795 + 4008599 * 2 ^ 59
def prefixEnd_4008599 : Nat := 4983230072969 + 3 ^ 40 * 4008599 * 2
def baseEnd_4008599 : Nat := 1372225358754978047784863

theorem tailTrace_4008599 : CollatzResearch.WordTrace tailWord_4008599 prefixEnd_4008599 1372225358754978047784863 := by
  unfold tailWord_4008599
  simp only [CollatzResearch.WordTrace]
  refine ⟨146205616804537912049388851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97470411203025274699592567 146205616804537912049388851)
  ·
    refine ⟨219308425206806868074083277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146205616804537912049388851 219308425206806868074083277)
    ·
      refine ⟨82240659452552575527781229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219308425206806868074083277 82240659452552575527781229)
      ·
        refine ⟨30840247294707215822917961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82240659452552575527781229 30840247294707215822917961)
        ·
          refine ⟨23130185471030411867188471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30840247294707215822917961 23130185471030411867188471)
          ·
            refine ⟨34695278206545617800782707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23130185471030411867188471 34695278206545617800782707)
            ·
              refine ⟨52042917309818426701174061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34695278206545617800782707 52042917309818426701174061)
              ·
                refine ⟨19516093991181910012940273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52042917309818426701174061 19516093991181910012940273)
                ·
                  refine ⟨14637070493386432509705205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19516093991181910012940273 14637070493386432509705205)
                  ·
                    refine ⟨1372225358754978047784863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14637070493386432509705205 1372225358754978047784863)
                    ·
                      rfl

theorem cell22_4008599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_4008599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008599 prefixEnd_4008599 := by exact prefixLift 4008599
  have htrace : WordTrace (prefixWord ++ tailWord_4008599) baseStart_4008599 baseEnd_4008599 := by
    simpa [prefixWord, tailWord_4008599, baseEnd_4008599] using wordTrace_append hprefix tailTrace_4008599
  have hstable : (prefixWord ++ tailWord_4008599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008599).length < 2 ^ (prefixWord ++ tailWord_4008599).sum := by decide
  have hdescent : baseEnd_4008599 < baseStart_4008599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008601 : List Nat := [1, 2, 1, 2, 1, 2, 7, 1, 5]
def baseStart_4008601 : Nat := 118140960795 + 4008601 * 2 ^ 59
def prefixEnd_4008601 : Nat := 4983230072969 + 3 ^ 40 * 4008601 * 2
def baseEnd_4008601 : Nat := 457408681131950236411619

theorem tailTrace_4008601 : CollatzResearch.WordTrace tailWord_4008601 prefixEnd_4008601 457408681131950236411619 := by
  unfold tailWord_4008601
  simp only [CollatzResearch.WordTrace]
  refine ⟨146205689750530666390961657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97470459833687110927307771 146205689750530666390961657)
  ·
    refine ⟨109654267312897999793221243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146205689750530666390961657 109654267312897999793221243)
    ·
      refine ⟨164481400969346999689831865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109654267312897999793221243 164481400969346999689831865)
      ·
        refine ⟨123361050727010249767373899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164481400969346999689831865 123361050727010249767373899)
        ·
          refine ⟨185041576090515374651060849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123361050727010249767373899 185041576090515374651060849)
          ·
            refine ⟨138781182067886530988295637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185041576090515374651060849 138781182067886530988295637)
            ·
              refine ⟨3252683954716090570038179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 138781182067886530988295637 3252683954716090570038179)
              ·
                refine ⟨4879025932074135855057269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3252683954716090570038179 4879025932074135855057269)
                ·
                  refine ⟨457408681131950236411619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4879025932074135855057269 457408681131950236411619)
                  ·
                    rfl

theorem cell22_4008601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 5].length) (baseStart_4008601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008601 prefixEnd_4008601 := by exact prefixLift 4008601
  have htrace : WordTrace (prefixWord ++ tailWord_4008601) baseStart_4008601 baseEnd_4008601 := by
    simpa [prefixWord, tailWord_4008601, baseEnd_4008601] using wordTrace_append hprefix tailTrace_4008601
  have hstable : (prefixWord ++ tailWord_4008601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008601).length < 2 ^ (prefixWord ++ tailWord_4008601).sum := by decide
  have hdescent : baseEnd_4008601 < baseStart_4008601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008622 : List Nat := [4, 1, 4, 1, 1, 1, 3, 3, 1, 3]
def baseStart_4008622 : Nat := 118140960795 + 4008622 * 2 ^ 59
def prefixEnd_4008622 : Nat := 4983230072969 + 3 ^ 40 * 4008622 * 2
def baseEnd_4008622 : Nat := 1372233232125013654459793

theorem tailTrace_4008622 : CollatzResearch.WordTrace tailWord_4008622 prefixEnd_4008622 1372233232125013654459793 := by
  unfold tailWord_4008622
  simp only [CollatzResearch.WordTrace]
  refine ⟨18275806960431823372184515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97470970455636391318317413 18275806960431823372184515)
  ·
    refine ⟨27413710440647735058276773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18275806960431823372184515 27413710440647735058276773)
    ·
      refine ⟨5140070707621450323426895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27413710440647735058276773 5140070707621450323426895)
      ·
        refine ⟨7710106061432175485140343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5140070707621450323426895 7710106061432175485140343)
        ·
          refine ⟨11565159092148263227710515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7710106061432175485140343 11565159092148263227710515)
          ·
            refine ⟨17347738638222394841565773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11565159092148263227710515 17347738638222394841565773)
            ·
              refine ⟨6505401989333398065587165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17347738638222394841565773 6505401989333398065587165)
              ·
                refine ⟨2439525746000024274595187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6505401989333398065587165 2439525746000024274595187)
                ·
                  refine ⟨3659288619000036411892781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439525746000024274595187 3659288619000036411892781)
                  ·
                    refine ⟨1372233232125013654459793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3659288619000036411892781 1372233232125013654459793)
                    ·
                      rfl

theorem cell22_4008622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_4008622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008622 prefixEnd_4008622 := by exact prefixLift 4008622
  have htrace : WordTrace (prefixWord ++ tailWord_4008622) baseStart_4008622 baseEnd_4008622 := by
    simpa [prefixWord, tailWord_4008622, baseEnd_4008622] using wordTrace_append hprefix tailTrace_4008622
  have hstable : (prefixWord ++ tailWord_4008622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008622).length < 2 ^ (prefixWord ++ tailWord_4008622).sum := by decide
  have hdescent : baseEnd_4008622 < baseStart_4008622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008676 : List Nat := [2, 3, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_4008676 : Nat := 118140960795 + 4008676 * 2 ^ 59
def prefixEnd_4008676 : Nat := 4983230072969 + 3 ^ 40 * 4008676 * 2
def baseEnd_4008676 : Nat := 1372251717428575513609627

theorem tailTrace_4008676 : CollatzResearch.WordTrace tailWord_4008676 prefixEnd_4008676 1372251717428575513609627 := by
  unfold tailWord_4008676
  simp only [CollatzResearch.WordTrace]
  refine ⟨73104212612629477099970941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97472283483505969466627921 73104212612629477099970941)
  ·
    refine ⟨27414079729736053912489103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73104212612629477099970941 27414079729736053912489103)
    ·
      refine ⟨41121119594604080868733655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27414079729736053912489103 41121119594604080868733655)
      ·
        refine ⟨61681679391906121303100483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41121119594604080868733655 61681679391906121303100483)
        ·
          refine ⟨92522519087859181954650725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61681679391906121303100483 92522519087859181954650725)
          ·
            refine ⟨17347972328973596616497011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92522519087859181954650725 17347972328973596616497011)
            ·
              refine ⟨26021958493460394924745517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17347972328973596616497011 26021958493460394924745517)
              ·
                refine ⟨9758234435047648096779569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26021958493460394924745517 9758234435047648096779569)
                ·
                  refine ⟨7318675826285736072584677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9758234435047648096779569 7318675826285736072584677)
                  ·
                    refine ⟨1372251717428575513609627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7318675826285736072584677 1372251717428575513609627)
                    ·
                      rfl

theorem cell22_4008676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_4008676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008676 prefixEnd_4008676 := by exact prefixLift 4008676
  have htrace : WordTrace (prefixWord ++ tailWord_4008676) baseStart_4008676 baseEnd_4008676 := by
    simpa [prefixWord, tailWord_4008676, baseEnd_4008676] using wordTrace_append hprefix tailTrace_4008676
  have hstable : (prefixWord ++ tailWord_4008676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008676).length < 2 ^ (prefixWord ++ tailWord_4008676).sum := by decide
  have hdescent : baseEnd_4008676 < baseStart_4008676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008811 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 4, 4]
def baseStart_4008811 : Nat := 118140960795 + 4008811 * 2 ^ 59
def prefixEnd_4008811 : Nat := 4983230072969 + 3 ^ 40 * 4008811 * 2
def baseEnd_4008811 : Nat := 1372297930687480161484213

theorem tailTrace_4008811 : CollatzResearch.WordTrace tailWord_4008811 prefixEnd_4008811 1372297930687480161484213 := by
  unfold tailWord_4008811
  simp only [CollatzResearch.WordTrace]
  refine ⟨146213349079769872256106287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97475566053179914837404191 146213349079769872256106287)
  ·
    refine ⟨219320023619654808384159431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146213349079769872256106287 219320023619654808384159431)
    ·
      refine ⟨328980035429482212576239147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219320023619654808384159431 328980035429482212576239147)
      ·
        refine ⟨493470053144223318864358721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328980035429482212576239147 493470053144223318864358721)
        ·
          refine ⟨370102539858167489148269041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493470053144223318864358721 370102539858167489148269041)
          ·
            refine ⟨277576904893625616861201781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370102539858167489148269041 277576904893625616861201781)
            ·
              refine ⟨26022834833777401580737667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277576904893625616861201781 26022834833777401580737667)
              ·
                refine ⟨39034252250666102371106501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26022834833777401580737667 39034252250666102371106501)
                ·
                  refine ⟨7318922296999894194582469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39034252250666102371106501 7318922296999894194582469)
                  ·
                    refine ⟨1372297930687480161484213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7318922296999894194582469 1372297930687480161484213)
                    ·
                      rfl

theorem cell22_4008811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 4].length) (baseStart_4008811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008811 prefixEnd_4008811 := by exact prefixLift 4008811
  have htrace : WordTrace (prefixWord ++ tailWord_4008811) baseStart_4008811 baseEnd_4008811 := by
    simpa [prefixWord, tailWord_4008811, baseEnd_4008811] using wordTrace_append hprefix tailTrace_4008811
  have hstable : (prefixWord ++ tailWord_4008811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008811).length < 2 ^ (prefixWord ++ tailWord_4008811).sum := by decide
  have hdescent : baseEnd_4008811 < baseStart_4008811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008875 : List Nat := [1, 1, 1, 1, 2, 1, 1, 10, 1, 3]
def baseStart_4008875 : Nat := 118140960795 + 4008875 * 2 ^ 59
def prefixEnd_4008875 : Nat := 4983230072969 + 3 ^ 40 * 4008875 * 2
def baseEnd_4008875 : Nat := 1372319839195405327884017

theorem tailTrace_4008875 : CollatzResearch.WordTrace tailWord_4008875 prefixEnd_4008875 1372319839195405327884017 := by
  unfold tailWord_4008875
  simp only [CollatzResearch.WordTrace]
  refine ⟨146215683351538011186436079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97477122234358674124290719 146215683351538011186436079)
  ·
    refine ⟨219323525027307016779654119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146215683351538011186436079 219323525027307016779654119)
    ·
      refine ⟨328985287540960525169481179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219323525027307016779654119 328985287540960525169481179)
      ·
        refine ⟨493477931311440787754221769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328985287540960525169481179 493477931311440787754221769)
        ·
          refine ⟨370108448483580590815666327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493477931311440787754221769 370108448483580590815666327)
          ·
            refine ⟨555162672725370886223499491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370108448483580590815666327 555162672725370886223499491)
            ·
              refine ⟨832744009088056329335249237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555162672725370886223499491 832744009088056329335249237)
              ·
                refine ⟨2439679714125165027349363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 832744009088056329335249237 2439679714125165027349363)
                ·
                  refine ⟨3659519571187747541024045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439679714125165027349363 3659519571187747541024045)
                  ·
                    refine ⟨1372319839195405327884017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3659519571187747541024045 1372319839195405327884017)
                    ·
                      rfl

theorem cell22_4008875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 1, 3].length) (baseStart_4008875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008875 prefixEnd_4008875 := by exact prefixLift 4008875
  have htrace : WordTrace (prefixWord ++ tailWord_4008875) baseStart_4008875 baseEnd_4008875 := by
    simpa [prefixWord, tailWord_4008875, baseEnd_4008875] using wordTrace_append hprefix tailTrace_4008875
  have hstable : (prefixWord ++ tailWord_4008875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008875).length < 2 ^ (prefixWord ++ tailWord_4008875).sum := by decide
  have hdescent : baseEnd_4008875 < baseStart_4008875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008877 : List Nat := [1, 5, 2, 3, 1, 2, 1, 7]
def baseStart_4008877 : Nat := 118140960795 + 4008877 * 2 ^ 59
def prefixEnd_4008877 : Nat := 4983230072969 + 3 ^ 40 * 4008877 * 2
def baseEnd_4008877 : Nat := 152480058204030887703779

theorem tailTrace_4008877 : CollatzResearch.WordTrace tailWord_4008877 prefixEnd_4008877 152480058204030887703779 := by
  unfold tailWord_4008877
  simp only [CollatzResearch.WordTrace]
  refine ⟨146215756297530765528008885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97477170865020510352005923 146215756297530765528008885)
  ·
    refine ⟨13707727152893509268250833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146215756297530765528008885 13707727152893509268250833)
    ·
      refine ⟨10280795364670131951188125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13707727152893509268250833 10280795364670131951188125)
      ·
        refine ⟨3855298261751299481695547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10280795364670131951188125 3855298261751299481695547)
        ·
          refine ⟨5782947392626949222543321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3855298261751299481695547 5782947392626949222543321)
          ·
            refine ⟨4337210544470211916907491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5782947392626949222543321 4337210544470211916907491)
            ·
              refine ⟨6505815816705317875361237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4337210544470211916907491 6505815816705317875361237)
              ·
                refine ⟨152480058204030887703779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6505815816705317875361237 152480058204030887703779)
                ·
                  rfl

theorem cell22_4008877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 7].length) (baseStart_4008877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008877 prefixEnd_4008877 := by exact prefixLift 4008877
  have htrace : WordTrace (prefixWord ++ tailWord_4008877) baseStart_4008877 baseEnd_4008877 := by
    simpa [prefixWord, tailWord_4008877, baseEnd_4008877] using wordTrace_append hprefix tailTrace_4008877
  have hstable : (prefixWord ++ tailWord_4008877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008877).length < 2 ^ (prefixWord ++ tailWord_4008877).sum := by decide
  have hdescent : baseEnd_4008877 < baseStart_4008877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008888 : List Nat := [2, 1, 2, 1, 2, 4, 2, 3, 5]
def baseStart_4008888 : Nat := 118140960795 + 4008888 * 2 ^ 59
def prefixEnd_4008888 : Nat := 4983230072969 + 3 ^ 40 * 4008888 * 2
def baseEnd_4008888 : Nat := 457441429787025875769659

theorem tailTrace_4008888 : CollatzResearch.WordTrace tailWord_4008888 prefixEnd_4008888 457441429787025875769659 := by
  unfold tailWord_4008888
  simp only [CollatzResearch.WordTrace]
  refine ⟨73108078750245457203329659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97477438333660609604439545 73108078750245457203329659)
  ·
    refine ⟨109662118125368185804994489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73108078750245457203329659 109662118125368185804994489)
    ·
      refine ⟨82246588594026139353745867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109662118125368185804994489 82246588594026139353745867)
      ·
        refine ⟨123369882891039209030618801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82246588594026139353745867 123369882891039209030618801)
        ·
          refine ⟨92527412168279406772964101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123369882891039209030618801 92527412168279406772964101)
          ·
            refine ⟨17348889781552388769930769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92527412168279406772964101 17348889781552388769930769)
            ·
              refine ⟨13011667336164291577448077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17348889781552388769930769 13011667336164291577448077)
              ·
                refine ⟨4879375251061609341543029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13011667336164291577448077 4879375251061609341543029)
                ·
                  refine ⟨457441429787025875769659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4879375251061609341543029 457441429787025875769659)
                  ·
                    rfl

theorem cell22_4008888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 5].length) (baseStart_4008888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008888 prefixEnd_4008888 := by exact prefixLift 4008888
  have htrace : WordTrace (prefixWord ++ tailWord_4008888) baseStart_4008888 baseEnd_4008888 := by
    simpa [prefixWord, tailWord_4008888, baseEnd_4008888] using wordTrace_append hprefix tailTrace_4008888
  have hstable : (prefixWord ++ tailWord_4008888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008888).length < 2 ^ (prefixWord ++ tailWord_4008888).sum := by decide
  have hdescent : baseEnd_4008888 < baseStart_4008888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008950 : List Nat := [5, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_4008950 : Nat := 118140960795 + 4008950 * 2 ^ 59
def prefixEnd_4008950 : Nat := 4983230072969 + 3 ^ 40 * 4008950 * 2
def baseEnd_4008950 : Nat := 457448504409376710752929

theorem tailTrace_4008950 : CollatzResearch.WordTrace tailWord_4008950 prefixEnd_4008950 457448504409376710752929 := by
  unfold tailWord_4008950
  simp only [CollatzResearch.WordTrace]
  refine ⟨9138651176641643687213519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97478945884177532663610869 9138651176641643687213519)
  ·
    refine ⟨13707976764962465530820279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9138651176641643687213519 13707976764962465530820279)
    ·
      refine ⟨20561965147443698296230419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13707976764962465530820279 20561965147443698296230419)
      ·
        refine ⟨30842947721165547444345629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20561965147443698296230419 30842947721165547444345629)
        ·
          refine ⟨11566105395437080291629611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30842947721165547444345629 11566105395437080291629611)
          ·
            refine ⟨17349158093155620437444417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11566105395437080291629611 17349158093155620437444417)
            ·
              refine ⟨13011868569866715328083313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17349158093155620437444417 13011868569866715328083313)
              ·
                refine ⟨9758901427400036496062485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13011868569866715328083313 9758901427400036496062485)
                ·
                  refine ⟨457448504409376710752929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9758901427400036496062485 457448504409376710752929)
                  ·
                    rfl

theorem cell22_4008950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_4008950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008950 prefixEnd_4008950 := by exact prefixLift 4008950
  have htrace : WordTrace (prefixWord ++ tailWord_4008950) baseStart_4008950 baseEnd_4008950 := by
    simpa [prefixWord, tailWord_4008950, baseEnd_4008950] using wordTrace_append hprefix tailTrace_4008950
  have hstable : (prefixWord ++ tailWord_4008950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008950).length < 2 ^ (prefixWord ++ tailWord_4008950).sum := by decide
  have hdescent : baseEnd_4008950 < baseStart_4008950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008999 : List Nat := [1, 1, 7, 1, 1, 2, 1, 3, 2, 3]
def baseStart_4008999 : Nat := 118140960795 + 4008999 * 2 ^ 59
def prefixEnd_4008999 : Nat := 4983230072969 + 3 ^ 40 * 4008999 * 2
def baseEnd_4008999 : Nat := 1372362286929510337783637

theorem tailTrace_4008999 : CollatzResearch.WordTrace tailWord_4008999 prefixEnd_4008999 1372362286929510337783637 := by
  unfold tailWord_4008999
  simp only [CollatzResearch.WordTrace]
  refine ⟨146220206003088780363950051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97480137335392520242633367 146220206003088780363950051)
  ·
    refine ⟨219330309004633170545925077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146220206003088780363950051 219330309004633170545925077)
    ·
      refine ⟨5140554117296089934670119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 219330309004633170545925077 5140554117296089934670119)
      ·
        refine ⟨7710831175944134902005179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5140554117296089934670119 7710831175944134902005179)
        ·
          refine ⟨11566246763916202353007769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7710831175944134902005179 11566246763916202353007769)
          ·
            refine ⟨8674685072937151764755827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11566246763916202353007769 8674685072937151764755827)
            ·
              refine ⟨13012027609405727647133741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8674685072937151764755827 13012027609405727647133741)
              ·
                refine ⟨4879510353527147867675153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13012027609405727647133741 4879510353527147867675153)
                ·
                  refine ⟨3659632765145360900756365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4879510353527147867675153 3659632765145360900756365)
                  ·
                    refine ⟨1372362286929510337783637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3659632765145360900756365 1372362286929510337783637)
                    ·
                      rfl

theorem cell22_4008999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_4008999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4008999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4008999 prefixEnd_4008999 := by exact prefixLift 4008999
  have htrace : WordTrace (prefixWord ++ tailWord_4008999) baseStart_4008999 baseEnd_4008999 := by
    simpa [prefixWord, tailWord_4008999, baseEnd_4008999] using wordTrace_append hprefix tailTrace_4008999
  have hstable : (prefixWord ++ tailWord_4008999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008999).length < 2 ^ (prefixWord ++ tailWord_4008999).sum := by decide
  have hdescent : baseEnd_4008999 < baseStart_4008999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009010 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 5, 3]
def baseStart_4009010 : Nat := 118140960795 + 4009010 * 2 ^ 59
def prefixEnd_4009010 : Nat := 4983230072969 + 3 ^ 40 * 4009010 * 2
def baseEnd_4009010 : Nat := 1372366052454309975758603

theorem tailTrace_4009010 : CollatzResearch.WordTrace tailWord_4009010 prefixEnd_4009010 1372366052454309975758603 := by
  unfold tailWord_4009010
  simp only [CollatzResearch.WordTrace]
  refine ⟨36555151801512232310650121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97480404804032619495066989 36555151801512232310650121)
  ·
    refine ⟨27416363851134174232987591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36555151801512232310650121 27416363851134174232987591)
    ·
      refine ⟨41124545776701261349481387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27416363851134174232987591 41124545776701261349481387)
      ·
        refine ⟨61686818665051892024222081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41124545776701261349481387 61686818665051892024222081)
        ·
          refine ⟨46265113998788919018166561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61686818665051892024222081 46265113998788919018166561)
          ·
            refine ⟨34698835499091689263624921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46265113998788919018166561 34698835499091689263624921)
            ·
              refine ⟨26024126624318766947718691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34698835499091689263624921 26024126624318766947718691)
              ·
                refine ⟨39036189936478150421578037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26024126624318766947718691 39036189936478150421578037)
                ·
                  refine ⟨3659642806544826602022941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39036189936478150421578037 3659642806544826602022941)
                  ·
                    refine ⟨1372366052454309975758603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3659642806544826602022941 1372366052454309975758603)
                    ·
                      rfl

theorem cell22_4009010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_4009010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009010 prefixEnd_4009010 := by exact prefixLift 4009010
  have htrace : WordTrace (prefixWord ++ tailWord_4009010) baseStart_4009010 baseEnd_4009010 := by
    simpa [prefixWord, tailWord_4009010, baseEnd_4009010] using wordTrace_append hprefix tailTrace_4009010
  have hstable : (prefixWord ++ tailWord_4009010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009010).length < 2 ^ (prefixWord ++ tailWord_4009010).sum := by decide
  have hdescent : baseEnd_4009010 < baseStart_4009010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009027 : List Nat := [1, 1, 1, 3, 1, 2, 4, 5, 1, 3]
def baseStart_4009027 : Nat := 118140960795 + 4009027 * 2 ^ 59
def prefixEnd_4009027 : Nat := 4983230072969 + 3 ^ 40 * 4009027 * 2
def baseEnd_4009027 : Nat := 1372371871901727598083551

theorem tailTrace_4009027 : CollatzResearch.WordTrace tailWord_4009027 prefixEnd_4009027 1372371871901727598083551 := by
  unfold tailWord_4009027
  simp only [CollatzResearch.WordTrace]
  refine ⟨146221227246987341145969335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97480818164658227430646223 146221227246987341145969335)
  ·
    refine ⟨219331840870481011718954003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146221227246987341145969335 219331840870481011718954003)
    ·
      refine ⟨328997761305721517578431005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219331840870481011718954003 328997761305721517578431005)
      ·
        refine ⟨123374160489645569091911627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328997761305721517578431005 123374160489645569091911627)
        ·
          refine ⟨185061240734468353637867441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123374160489645569091911627 185061240734468353637867441)
          ·
            refine ⟨138795930550851265228400581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185061240734468353637867441 138795930550851265228400581)
            ·
              refine ⟨26024236978284612230325109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138795930550851265228400581 26024236978284612230325109)
              ·
                refine ⟨2439772216714182396592979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26024236978284612230325109 2439772216714182396592979)
                ·
                  refine ⟨3659658325071273594889469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439772216714182396592979 3659658325071273594889469)
                  ·
                    refine ⟨1372371871901727598083551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3659658325071273594889469 1372371871901727598083551)
                    ·
                      rfl

theorem cell22_4009027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 1, 3].length) (baseStart_4009027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009027 prefixEnd_4009027 := by exact prefixLift 4009027
  have htrace : WordTrace (prefixWord ++ tailWord_4009027) baseStart_4009027 baseEnd_4009027 := by
    simpa [prefixWord, tailWord_4009027, baseEnd_4009027] using wordTrace_append hprefix tailTrace_4009027
  have hstable : (prefixWord ++ tailWord_4009027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009027).length < 2 ^ (prefixWord ++ tailWord_4009027).sum := by decide
  have hdescent : baseEnd_4009027 < baseStart_4009027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009046 : List Nat := [5, 2, 2, 1, 3, 1, 1, 7]
def baseStart_4009046 : Nat := 118140960795 + 4009046 * 2 ^ 59
def prefixEnd_4009046 : Nat := 4983230072969 + 3 ^ 40 * 4009046 * 2
def baseEnd_4009046 : Nat := 152486486221113097984277

theorem tailTrace_4009046 : CollatzResearch.WordTrace tailWord_4009046 prefixEnd_4009046 152486486221113097984277 := by
  unfold tailWord_4009046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9138870014619906711931937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97481280155945671593940661 9138870014619906711931937)
  ·
    refine ⟨6854152510964930033948953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9138870014619906711931937 6854152510964930033948953)
    ·
      refine ⟨5140614383223697525461715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6854152510964930033948953 5140614383223697525461715)
      ·
        refine ⟨7710921574835546288192573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5140614383223697525461715 7710921574835546288192573)
        ·
          refine ⟨2891595590563329858072215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7710921574835546288192573 2891595590563329858072215)
          ·
            refine ⟨4337393385844994787108323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2891595590563329858072215 4337393385844994787108323)
            ·
              refine ⟨6506090078767492180662485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4337393385844994787108323 6506090078767492180662485)
              ·
                refine ⟨152486486221113097984277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6506090078767492180662485 152486486221113097984277)
                ·
                  rfl

theorem cell22_4009046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_4009046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009046 prefixEnd_4009046 := by exact prefixLift 4009046
  have htrace : WordTrace (prefixWord ++ tailWord_4009046) baseStart_4009046 baseEnd_4009046 := by
    simpa [prefixWord, tailWord_4009046, baseEnd_4009046] using wordTrace_append hprefix tailTrace_4009046
  have hstable : (prefixWord ++ tailWord_4009046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009046).length < 2 ^ (prefixWord ++ tailWord_4009046).sum := by decide
  have hdescent : baseEnd_4009046 < baseStart_4009046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009102 : List Nat := [4, 1, 1, 3, 2, 2, 2, 1, 6]
def baseStart_4009102 : Nat := 118140960795 + 4009102 * 2 ^ 59
def prefixEnd_4009102 : Nat := 4983230072969 + 3 ^ 40 * 4009102 * 2
def baseEnd_4009102 : Nat := 457465848644817467486107

theorem tailTrace_4009102 : CollatzResearch.WordTrace tailWord_4009102 prefixEnd_4009102 457465848644817467486107 := by
  unfold tailWord_4009102
  simp only [CollatzResearch.WordTrace]
  refine ⟨18277995340214453619368695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97482641814477085969966373 18277995340214453619368695)
  ·
    refine ⟨27416993010321680429053043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18277995340214453619368695 27416993010321680429053043)
    ·
      refine ⟨41125489515482520643579565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27416993010321680429053043 41125489515482520643579565)
      ·
        refine ⟨15422058568305945241342337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41125489515482520643579565 15422058568305945241342337)
        ·
          refine ⟨11566543926229458931006753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15422058568305945241342337 11566543926229458931006753)
          ·
            refine ⟨8674907944672094198255065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11566543926229458931006753 8674907944672094198255065)
            ·
              refine ⟨6506180958504070648691299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8674907944672094198255065 6506180958504070648691299)
              ·
                refine ⟨9759271437756105973036949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6506180958504070648691299 9759271437756105973036949)
                ·
                  refine ⟨457465848644817467486107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9759271437756105973036949 457465848644817467486107)
                  ·
                    rfl

theorem cell22_4009102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_4009102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009102 prefixEnd_4009102 := by exact prefixLift 4009102
  have htrace : WordTrace (prefixWord ++ tailWord_4009102) baseStart_4009102 baseEnd_4009102 := by
    simpa [prefixWord, tailWord_4009102, baseEnd_4009102] using wordTrace_append hprefix tailTrace_4009102
  have hstable : (prefixWord ++ tailWord_4009102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009102).length < 2 ^ (prefixWord ++ tailWord_4009102).sum := by decide
  have hdescent : baseEnd_4009102 < baseStart_4009102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009252 : List Nat := [2, 3, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_4009252 : Nat := 118140960795 + 4009252 * 2 ^ 59
def prefixEnd_4009252 : Nat := 4983230072969 + 3 ^ 40 * 4009252 * 2
def baseEnd_4009252 : Nat := 1372448893999902011207861

theorem tailTrace_4009252 : CollatzResearch.WordTrace tailWord_4009252 prefixEnd_4009252 1372448893999902011207861 := by
  unfold tailWord_4009252
  simp only [CollatzResearch.WordTrace]
  refine ⟨73114716835586102286455005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97486289114114803048606673 73114716835586102286455005)
  ·
    refine ⟨27418018813344788357420627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73114716835586102286455005 27418018813344788357420627)
    ·
      refine ⟨41127028220017182536130941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27418018813344788357420627 41127028220017182536130941)
      ·
        refine ⟨15422635582506443451049103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41127028220017182536130941 15422635582506443451049103)
        ·
          refine ⟨23133953373759665176573655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15422635582506443451049103 23133953373759665176573655)
          ·
            refine ⟨34700930060639497764860483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23133953373759665176573655 34700930060639497764860483)
            ·
              refine ⟨52051395090959246647290725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34700930060639497764860483 52051395090959246647290725)
              ·
                refine ⟨9759636579554858746367011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52051395090959246647290725 9759636579554858746367011)
                ·
                  refine ⟨14639454869332288119550517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9759636579554858746367011 14639454869332288119550517)
                  ·
                    refine ⟨1372448893999902011207861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14639454869332288119550517 1372448893999902011207861)
                    ·
                      rfl

theorem cell22_4009252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_4009252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009252 prefixEnd_4009252 := by exact prefixLift 4009252
  have htrace : WordTrace (prefixWord ++ tailWord_4009252) baseStart_4009252 baseEnd_4009252 := by
    simpa [prefixWord, tailWord_4009252, baseEnd_4009252] using wordTrace_append hprefix tailTrace_4009252
  have hstable : (prefixWord ++ tailWord_4009252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009252).length < 2 ^ (prefixWord ++ tailWord_4009252).sum := by decide
  have hdescent : baseEnd_4009252 < baseStart_4009252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009256 : List Nat := [2, 1, 5, 1, 2, 1, 4, 1, 1, 4]
def baseStart_4009256 : Nat := 118140960795 + 4009256 * 2 ^ 59
def prefixEnd_4009256 : Nat := 4983230072969 + 3 ^ 40 * 4009256 * 2
def baseEnd_4009256 : Nat := 1372450263281647334107849

theorem tailTrace_4009256 : CollatzResearch.WordTrace tailWord_4009256 prefixEnd_4009256 1372450263281647334107849 := by
  unfold tailWord_4009256
  simp only [CollatzResearch.WordTrace]
  refine ⟨73114789781578856628027811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97486386375438475504037081 73114789781578856628027811)
  ·
    refine ⟨109672184672368284942041717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73114789781578856628027811 109672184672368284942041717)
    ·
      refine ⟨10281767313034526713316411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109672184672368284942041717 10281767313034526713316411)
      ·
        refine ⟨15422650969551790069974617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10281767313034526713316411 15422650969551790069974617)
        ·
          refine ⟨11566988227163842552480963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15422650969551790069974617 11566988227163842552480963)
          ·
            refine ⟨17350482340745763828721445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11566988227163842552480963 17350482340745763828721445)
            ·
              refine ⟨3253215438889830717885271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17350482340745763828721445 3253215438889830717885271)
              ·
                refine ⟨4879823158334746076827907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3253215438889830717885271 4879823158334746076827907)
                ·
                  refine ⟨7319734737502119115241861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4879823158334746076827907 7319734737502119115241861)
                  ·
                    refine ⟨1372450263281647334107849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7319734737502119115241861 1372450263281647334107849)
                    ·
                      rfl

theorem cell22_4009256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_4009256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009256 prefixEnd_4009256 := by exact prefixLift 4009256
  have htrace : WordTrace (prefixWord ++ tailWord_4009256) baseStart_4009256 baseEnd_4009256 := by
    simpa [prefixWord, tailWord_4009256, baseEnd_4009256] using wordTrace_append hprefix tailTrace_4009256
  have hstable : (prefixWord ++ tailWord_4009256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009256).length < 2 ^ (prefixWord ++ tailWord_4009256).sum := by decide
  have hdescent : baseEnd_4009256 < baseStart_4009256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009269 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 4, 3]
def baseStart_4009269 : Nat := 118140960795 + 4009269 * 2 ^ 59
def prefixEnd_4009269 : Nat := 4983230072969 + 3 ^ 40 * 4009269 * 2
def baseEnd_4009269 : Nat := 1372454713447319633532809

theorem tailTrace_4009269 : CollatzResearch.WordTrace tailWord_4009269 prefixEnd_4009269 1372454713447319633532809 := by
  unfold tailWord_4009269
  simp only [CollatzResearch.WordTrace]
  refine ⟨146230053712110616476278861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97486702474740410984185907 146230053712110616476278861)
  ·
    refine ⟨54836270142041481178604573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146230053712110616476278861 54836270142041481178604573)
    ·
      refine ⟨20563601303265555441976715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54836270142041481178604573 20563601303265555441976715)
      ·
        refine ⟨30845401954898333162965073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20563601303265555441976715 30845401954898333162965073)
        ·
          refine ⟨23134051466173749872223805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30845401954898333162965073 23134051466173749872223805)
          ·
            refine ⟨8675269299815156202083927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23134051466173749872223805 8675269299815156202083927)
            ·
              refine ⟨13012903949722734303125891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8675269299815156202083927 13012903949722734303125891)
              ·
                refine ⟨19519355924584101454688837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13012903949722734303125891 19519355924584101454688837)
                ·
                  refine ⟨3659879235859519022754157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19519355924584101454688837 3659879235859519022754157)
                  ·
                    refine ⟨1372454713447319633532809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3659879235859519022754157 1372454713447319633532809)
                    ·
                      rfl

theorem cell22_4009269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_4009269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009269 prefixEnd_4009269 := by exact prefixLift 4009269
  have htrace : WordTrace (prefixWord ++ tailWord_4009269) baseStart_4009269 baseEnd_4009269 := by
    simpa [prefixWord, tailWord_4009269, baseEnd_4009269] using wordTrace_append hprefix tailTrace_4009269
  have hstable : (prefixWord ++ tailWord_4009269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009269).length < 2 ^ (prefixWord ++ tailWord_4009269).sum := by decide
  have hdescent : baseEnd_4009269 < baseStart_4009269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009284 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_4009284 : Nat := 118140960795 + 4009284 * 2 ^ 59
def prefixEnd_4009284 : Nat := 4983230072969 + 3 ^ 40 * 4009284 * 2
def baseEnd_4009284 : Nat := 1372459848253864594407763

theorem tailTrace_4009284 : CollatzResearch.WordTrace tailWord_4009284 prefixEnd_4009284 1372459848253864594407763 := by
  unfold tailWord_4009284
  simp only [CollatzResearch.WordTrace]
  refine ⟨73115300403528137019037453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97487067204704182692049937 73115300403528137019037453)
  ·
    refine ⟨27418237651323051382139045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73115300403528137019037453 27418237651323051382139045)
    ·
      refine ⟨5140919559623072134151071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27418237651323051382139045 5140919559623072134151071)
      ·
        refine ⟨7711379339434608201226607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5140919559623072134151071 7711379339434608201226607)
        ·
          refine ⟨11567069009151912301839911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7711379339434608201226607 11567069009151912301839911)
          ·
            refine ⟨17350603513727868452759867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11567069009151912301839911 17350603513727868452759867)
            ·
              refine ⟨26025905270591802679139801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17350603513727868452759867 26025905270591802679139801)
              ·
                refine ⟨19519428952943852009354851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26025905270591802679139801 19519428952943852009354851)
                ·
                  refine ⟨29279143429415778014032277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19519428952943852009354851 29279143429415778014032277)
                  ·
                    refine ⟨1372459848253864594407763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29279143429415778014032277 1372459848253864594407763)
                    ·
                      rfl

theorem cell22_4009284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_4009284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009284 prefixEnd_4009284 := by exact prefixLift 4009284
  have htrace : WordTrace (prefixWord ++ tailWord_4009284) baseStart_4009284 baseEnd_4009284 := by
    simpa [prefixWord, tailWord_4009284, baseEnd_4009284] using wordTrace_append hprefix tailTrace_4009284
  have hstable : (prefixWord ++ tailWord_4009284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009284).length < 2 ^ (prefixWord ++ tailWord_4009284).sum := by decide
  have hdescent : baseEnd_4009284 < baseStart_4009284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009295 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 3, 8]
def baseStart_4009295 : Nat := 118140960795 + 4009295 * 2 ^ 59
def prefixEnd_4009295 : Nat := 4983230072969 + 3 ^ 40 * 4009295 * 2
def baseEnd_4009295 : Nat := 1372463613778664232382729

theorem tailTrace_4009295 : CollatzResearch.WordTrace tailWord_4009295 prefixEnd_4009295 1372463613778664232382729 := by
  unfold tailWord_4009295
  simp only [CollatzResearch.WordTrace]
  refine ⟨146231002010016422916725339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97487334673344281944483559 146231002010016422916725339)
  ·
    refine ⟨219346503015024634375088009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146231002010016422916725339 219346503015024634375088009)
    ·
      refine ⟨164509877261268475781316007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219346503015024634375088009 164509877261268475781316007)
      ·
        refine ⟨246764815891902713671974011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164509877261268475781316007 246764815891902713671974011)
        ·
          refine ⟨370147223837854070507961017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246764815891902713671974011 370147223837854070507961017)
          ·
            refine ⟨277610417878390552880970763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370147223837854070507961017 277610417878390552880970763)
            ·
              refine ⟨416415626817585829321456145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277610417878390552880970763 416415626817585829321456145)
              ·
                refine ⟨312311720113189371991092109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416415626817585829321456145 312311720113189371991092109)
                ·
                  refine ⟨117116895042446014496659541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312311720113189371991092109 117116895042446014496659541)
                  ·
                    refine ⟨1372463613778664232382729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117116895042446014496659541 1372463613778664232382729)
                    ·
                      rfl

theorem cell22_4009295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_4009295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009295 prefixEnd_4009295 := by exact prefixLift 4009295
  have htrace : WordTrace (prefixWord ++ tailWord_4009295) baseStart_4009295 baseEnd_4009295 := by
    simpa [prefixWord, tailWord_4009295, baseEnd_4009295] using wordTrace_append hprefix tailTrace_4009295
  have hstable : (prefixWord ++ tailWord_4009295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009295).length < 2 ^ (prefixWord ++ tailWord_4009295).sum := by decide
  have hdescent : baseEnd_4009295 < baseStart_4009295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009327 : List Nat := [1, 1, 2, 1, 3, 1, 4, 4, 5]
def baseStart_4009327 : Nat := 118140960795 + 4009327 * 2 ^ 59
def prefixEnd_4009327 : Nat := 4983230072969 + 3 ^ 40 * 4009327 * 2
def baseEnd_4009327 : Nat := 457491522677542271860877

theorem tailTrace_4009327 : CollatzResearch.WordTrace tailWord_4009327 prefixEnd_4009327 457491522677542271860877 := by
  unfold tailWord_4009327
  simp only [CollatzResearch.WordTrace]
  refine ⟨146232169145900492381890235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97488112763933661587926823 146232169145900492381890235)
  ·
    refine ⟨219348253718850738572835353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146232169145900492381890235 219348253718850738572835353)
    ·
      refine ⟨164511190289138053929626515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219348253718850738572835353 164511190289138053929626515)
      ·
        refine ⟨246766785433707080894439773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164511190289138053929626515 246766785433707080894439773)
        ·
          refine ⟨92537544537640155335414915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246766785433707080894439773 92537544537640155335414915)
          ·
            refine ⟨138806316806460233003122373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92537544537640155335414915 138806316806460233003122373)
            ·
              refine ⟨26026184401211293688085445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138806316806460233003122373 26026184401211293688085445)
              ·
                refine ⟨4879909575227117566516021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26026184401211293688085445 4879909575227117566516021)
                ·
                  refine ⟨457491522677542271860877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4879909575227117566516021 457491522677542271860877)
                  ·
                    rfl

theorem cell22_4009327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 5].length) (baseStart_4009327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009327 prefixEnd_4009327 := by exact prefixLift 4009327
  have htrace : WordTrace (prefixWord ++ tailWord_4009327) baseStart_4009327 baseEnd_4009327 := by
    simpa [prefixWord, tailWord_4009327, baseEnd_4009327] using wordTrace_append hprefix tailTrace_4009327
  have hstable : (prefixWord ++ tailWord_4009327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009327).length < 2 ^ (prefixWord ++ tailWord_4009327).sum := by decide
  have hdescent : baseEnd_4009327 < baseStart_4009327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009419 : List Nat := [1, 1, 1, 1, 3, 3, 5, 1, 2, 4]
def baseStart_4009419 : Nat := 118140960795 + 4009419 * 2 ^ 59
def prefixEnd_4009419 : Nat := 4983230072969 + 3 ^ 40 * 4009419 * 2
def baseEnd_4009419 : Nat := 1372506061512769242282349

theorem tailTrace_4009419 : CollatzResearch.WordTrace tailWord_4009419 prefixEnd_4009419 1372506061512769242282349 := by
  unfold tailWord_4009419
  simp only [CollatzResearch.WordTrace]
  refine ⟨146235524661567192094239311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97490349774378128062826207 146235524661567192094239311)
  ·
    refine ⟨219353286992350788141358967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146235524661567192094239311 219353286992350788141358967)
    ·
      refine ⟨329029930488526182212038451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219353286992350788141358967 329029930488526182212038451)
      ·
        refine ⟨493544895732789273318057677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329029930488526182212038451 493544895732789273318057677)
        ·
          refine ⟨185079335899795977494271629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493544895732789273318057677 185079335899795977494271629)
          ·
            refine ⟨69404750962423491560351861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185079335899795977494271629 69404750962423491560351861)
            ·
              refine ⟨6506695402727202333782987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69404750962423491560351861 6506695402727202333782987)
              ·
                refine ⟨9760043104090803500674481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6506695402727202333782987 9760043104090803500674481)
                ·
                  refine ⟨7320032328068102625505861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9760043104090803500674481 7320032328068102625505861)
                  ·
                    refine ⟨1372506061512769242282349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7320032328068102625505861 1372506061512769242282349)
                    ·
                      rfl

theorem cell22_4009419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 4].length) (baseStart_4009419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009419 prefixEnd_4009419 := by exact prefixLift 4009419
  have htrace : WordTrace (prefixWord ++ tailWord_4009419) baseStart_4009419 baseEnd_4009419 := by
    simpa [prefixWord, tailWord_4009419, baseEnd_4009419] using wordTrace_append hprefix tailTrace_4009419
  have hstable : (prefixWord ++ tailWord_4009419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009419).length < 2 ^ (prefixWord ++ tailWord_4009419).sum := by decide
  have hdescent : baseEnd_4009419 < baseStart_4009419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009479 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 7]
def baseStart_4009479 : Nat := 118140960795 + 4009479 * 2 ^ 59
def prefixEnd_4009479 : Nat := 4983230072969 + 3 ^ 40 * 4009479 * 2
def baseEnd_4009479 : Nat := 457508866912983028594055

theorem tailTrace_4009479 : CollatzResearch.WordTrace tailWord_4009479 prefixEnd_4009479 457508866912983028594055 := by
  unfold tailWord_4009479
  simp only [CollatzResearch.WordTrace]
  refine ⟨146237713041349822341423491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97491808694233214894282327 146237713041349822341423491)
  ·
    refine ⟨219356569562024733512135237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146237713041349822341423491 219356569562024733512135237)
    ·
      refine ⟨41129356792879637533525357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219356569562024733512135237 41129356792879637533525357)
      ·
        refine ⟨15423508797329864075072009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41129356792879637533525357 15423508797329864075072009)
        ·
          refine ⟨11567631597997398056304007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15423508797329864075072009 11567631597997398056304007)
          ·
            refine ⟨17351447396996097084456011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11567631597997398056304007 17351447396996097084456011)
            ·
              refine ⟨26027171095494145626684017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17351447396996097084456011 26027171095494145626684017)
              ·
                refine ⟨19520378321620609220013013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26027171095494145626684017 19520378321620609220013013)
                ·
                  refine ⟨457508866912983028594055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19520378321620609220013013 457508866912983028594055)
                  ·
                    rfl

theorem cell22_4009479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 7].length) (baseStart_4009479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009479 prefixEnd_4009479 := by exact prefixLift 4009479
  have htrace : WordTrace (prefixWord ++ tailWord_4009479) baseStart_4009479 baseEnd_4009479 := by
    simpa [prefixWord, tailWord_4009479, baseEnd_4009479] using wordTrace_append hprefix tailTrace_4009479
  have hstable : (prefixWord ++ tailWord_4009479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009479).length < 2 ^ (prefixWord ++ tailWord_4009479).sum := by decide
  have hdescent : baseEnd_4009479 < baseStart_4009479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009485 : List Nat := [1, 7, 1, 1, 3, 1, 8]
def baseStart_4009485 : Nat := 118140960795 + 4009485 * 2 ^ 59
def prefixEnd_4009485 : Nat := 4983230072969 + 3 ^ 40 * 4009485 * 2
def baseEnd_4009485 : Nat := 50834394617095076671561

theorem tailTrace_4009485 : CollatzResearch.WordTrace tailWord_4009485 prefixEnd_4009485 50834394617095076671561 := by
  unfold tailWord_4009485
  simp only [CollatzResearch.WordTrace]
  refine ⟨146237931879328085366141909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97491954586218723577427939 146237931879328085366141909)
  ·
    refine ⟨3427451528421752000768951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 146237931879328085366141909 3427451528421752000768951)
    ·
      refine ⟨5141177292632628001153427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3427451528421752000768951 5141177292632628001153427)
      ·
        refine ⟨7711765938948942001730141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5141177292632628001153427 7711765938948942001730141)
        ·
          refine ⟨2891912227105853250648803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7711765938948942001730141 2891912227105853250648803)
          ·
            refine ⟨4337868340658779875973205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2891912227105853250648803 4337868340658779875973205)
            ·
              refine ⟨50834394617095076671561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4337868340658779875973205 50834394617095076671561)
              ·
                rfl

theorem cell22_4009485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 8].length) (baseStart_4009485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009485 prefixEnd_4009485 := by exact prefixLift 4009485
  have htrace : WordTrace (prefixWord ++ tailWord_4009485) baseStart_4009485 baseEnd_4009485 := by
    simpa [prefixWord, tailWord_4009485, baseEnd_4009485] using wordTrace_append hprefix tailTrace_4009485
  have hstable : (prefixWord ++ tailWord_4009485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009485).length < 2 ^ (prefixWord ++ tailWord_4009485).sum := by decide
  have hdescent : baseEnd_4009485 < baseStart_4009485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009500 : List Nat := [2, 2, 3, 1, 2, 1, 5, 2, 1, 3]
def baseStart_4009500 : Nat := 118140960795 + 4009500 * 2 ^ 59
def prefixEnd_4009500 : Nat := 4983230072969 + 3 ^ 40 * 4009500 * 2
def baseEnd_4009500 : Nat := 1372533789468112031007101

theorem tailTrace_4009500 : CollatzResearch.WordTrace tailWord_4009500 prefixEnd_4009500 1372533789468112031007101 := by
  unfold tailWord_4009500
  simp only [CollatzResearch.WordTrace]
  refine ⟨73119239487136871463968977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97492319316182495285291969 73119239487136871463968977)
  ·
    refine ⟨54839429615352653597976733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73119239487136871463968977 54839429615352653597976733)
    ·
      refine ⟨20564786105757245099241275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54839429615352653597976733 20564786105757245099241275)
      ·
        refine ⟨30847179158635867648861913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20564786105757245099241275 30847179158635867648861913)
        ·
          refine ⟨23135384368976900736646435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30847179158635867648861913 23135384368976900736646435)
          ·
            refine ⟨34703076553465351104969653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23135384368976900736646435 34703076553465351104969653)
            ·
              refine ⟨3253413426887376666090905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34703076553465351104969653 3253413426887376666090905)
              ·
                refine ⟨2440060070165532499568179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3253413426887376666090905 2440060070165532499568179)
                ·
                  refine ⟨3660090105248298749352269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2440060070165532499568179 3660090105248298749352269)
                  ·
                    refine ⟨1372533789468112031007101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3660090105248298749352269 1372533789468112031007101)
                    ·
                      rfl

theorem cell22_4009500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_4009500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009500 prefixEnd_4009500 := by exact prefixLift 4009500
  have htrace : WordTrace (prefixWord ++ tailWord_4009500) baseStart_4009500 baseEnd_4009500 := by
    simpa [prefixWord, tailWord_4009500, baseEnd_4009500] using wordTrace_append hprefix tailTrace_4009500
  have hstable : (prefixWord ++ tailWord_4009500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009500).length < 2 ^ (prefixWord ++ tailWord_4009500).sum := by decide
  have hdescent : baseEnd_4009500 < baseStart_4009500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009509 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 3, 4]
def baseStart_4009509 : Nat := 118140960795 + 4009509 * 2 ^ 59
def prefixEnd_4009509 : Nat := 4983230072969 + 3 ^ 40 * 4009509 * 2
def baseEnd_4009509 : Nat := 1372536870352039007532073

theorem tailTrace_4009509 : CollatzResearch.WordTrace tailWord_4009509 prefixEnd_4009509 1372536870352039007532073 := by
  unfold tailWord_4009509
  simp only [CollatzResearch.WordTrace]
  refine ⟨146238807231241137465015581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97492538154160758310010387 146238807231241137465015581)
  ·
    refine ⟨54839552711715426549380843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146238807231241137465015581 54839552711715426549380843)
    ·
      refine ⟨82259329067573139824071265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54839552711715426549380843 82259329067573139824071265)
      ·
        refine ⟨61694496800679854868053449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82259329067573139824071265 61694496800679854868053449)
        ·
          refine ⟨46270872600509891151040087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61694496800679854868053449 46270872600509891151040087)
          ·
            refine ⟨69406308900764836726560131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46270872600509891151040087 69406308900764836726560131)
            ·
              refine ⟨104109463351147255089840197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69406308900764836726560131 104109463351147255089840197)
              ·
                refine ⟨19520524378340110329345037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104109463351147255089840197 19520524378340110329345037)
                ·
                  refine ⟨7320196641877541373504389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19520524378340110329345037 7320196641877541373504389)
                  ·
                    refine ⟨1372536870352039007532073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7320196641877541373504389 1372536870352039007532073)
                    ·
                      rfl

theorem cell22_4009509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_4009509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009509 prefixEnd_4009509 := by exact prefixLift 4009509
  have htrace : WordTrace (prefixWord ++ tailWord_4009509) baseStart_4009509 baseEnd_4009509 := by
    simpa [prefixWord, tailWord_4009509, baseEnd_4009509] using wordTrace_append hprefix tailTrace_4009509
  have hstable : (prefixWord ++ tailWord_4009509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009509).length < 2 ^ (prefixWord ++ tailWord_4009509).sum := by decide
  have hdescent : baseEnd_4009509 < baseStart_4009509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009541 : List Nat := [1, 3, 1, 1, 1, 4, 2, 5, 4]
def baseStart_4009541 : Nat := 118140960795 + 4009541 * 2 ^ 59
def prefixEnd_4009541 : Nat := 4983230072969 + 3 ^ 40 * 4009541 * 2
def baseEnd_4009541 : Nat := 457515941535333863577325

theorem tailTrace_4009541 : CollatzResearch.WordTrace tailWord_4009541 prefixEnd_4009541 457515941535333863577325 := by
  unfold tailWord_4009541
  simp only [CollatzResearch.WordTrace]
  refine ⟨146239974367125206930180477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97493316244750137953453651 146239974367125206930180477)
  ·
    refine ⟨54839990387671952598817679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146239974367125206930180477 54839990387671952598817679)
    ·
      refine ⟨82259985581507928898226519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54839990387671952598817679 82259985581507928898226519)
      ·
        refine ⟨123389978372261893347339779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82259985581507928898226519 123389978372261893347339779)
        ·
          refine ⟨185084967558392840021009669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123389978372261893347339779 185084967558392840021009669)
          ·
            refine ⟨34703431417198657503939313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185084967558392840021009669 34703431417198657503939313)
            ·
              refine ⟨26027573562898993127954485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34703431417198657503939313 26027573562898993127954485)
              ·
                refine ⟨2440085021521780605745733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26027573562898993127954485 2440085021521780605745733)
                ·
                  refine ⟨457515941535333863577325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2440085021521780605745733 457515941535333863577325)
                  ·
                    rfl

theorem cell22_4009541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_4009541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009541 prefixEnd_4009541 := by exact prefixLift 4009541
  have htrace : WordTrace (prefixWord ++ tailWord_4009541) baseStart_4009541 baseEnd_4009541 := by
    simpa [prefixWord, tailWord_4009541, baseEnd_4009541] using wordTrace_append hprefix tailTrace_4009541
  have hstable : (prefixWord ++ tailWord_4009541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009541).length < 2 ^ (prefixWord ++ tailWord_4009541).sum := by decide
  have hdescent : baseEnd_4009541 < baseStart_4009541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009573 : List Nat := [1, 3, 1, 3, 3, 1, 2, 3, 2, 3]
def baseStart_4009573 : Nat := 118140960795 + 4009573 * 2 ^ 59
def prefixEnd_4009573 : Nat := 4983230072969 + 3 ^ 40 * 4009573 * 2
def baseEnd_4009573 : Nat := 1372558778859964173931877

theorem tailTrace_4009573 : CollatzResearch.WordTrace tailWord_4009573 prefixEnd_4009573 1372558778859964173931877 := by
  unfold tailWord_4009573
  simp only [CollatzResearch.WordTrace]
  refine ⟨146241141503009276395345373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97494094335339517596896915 146241141503009276395345373)
  ·
    refine ⟨54840428063628478648254515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146241141503009276395345373 54840428063628478648254515)
    ·
      refine ⟨82260642095442717972381773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54840428063628478648254515 82260642095442717972381773)
      ·
        refine ⟨30847740785791019239643165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82260642095442717972381773 30847740785791019239643165)
        ·
          refine ⟨11567902794671632214866187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30847740785791019239643165 11567902794671632214866187)
          ·
            refine ⟨17351854192007448322299281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11567902794671632214866187 17351854192007448322299281)
            ·
              refine ⟨13013890644005586241724461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17351854192007448322299281 13013890644005586241724461)
              ·
                refine ⟨4880208991502094840646673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13013890644005586241724461 4880208991502094840646673)
                ·
                  refine ⟨3660156743626571130485005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4880208991502094840646673 3660156743626571130485005)
                  ·
                    refine ⟨1372558778859964173931877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3660156743626571130485005 1372558778859964173931877)
                    ·
                      rfl

theorem cell22_4009573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_4009573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009573 prefixEnd_4009573 := by exact prefixLift 4009573
  have htrace : WordTrace (prefixWord ++ tailWord_4009573) baseStart_4009573 baseEnd_4009573 := by
    simpa [prefixWord, tailWord_4009573, baseEnd_4009573] using wordTrace_append hprefix tailTrace_4009573
  have hstable : (prefixWord ++ tailWord_4009573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009573).length < 2 ^ (prefixWord ++ tailWord_4009573).sum := by decide
  have hdescent : baseEnd_4009573 < baseStart_4009573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009644 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 4, 8]
def baseStart_4009644 : Nat := 118140960795 + 4009644 * 2 ^ 59
def prefixEnd_4009644 : Nat := 4983230072969 + 3 ^ 40 * 4009644 * 2
def baseEnd_4009644 : Nat := 1372583083610943655406659

theorem tailTrace_4009644 : CollatzResearch.WordTrace tailWord_4009644 prefixEnd_4009644 1372583083610943655406659 := by
  unfold tailWord_4009644
  simp only [CollatzResearch.WordTrace]
  refine ⟨73121865542876027760589993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97495820723834703680786657 73121865542876027760589993)
  ·
    refine ⟨54841399157157020820442495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73121865542876027760589993 54841399157157020820442495)
    ·
      refine ⟨82262098735735531230663743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54841399157157020820442495 82262098735735531230663743)
      ·
        refine ⟨123393148103603296845995615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82262098735735531230663743 123393148103603296845995615)
        ·
          refine ⟨185089722155404945268993423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123393148103603296845995615 185089722155404945268993423)
          ·
            refine ⟨277634583233107417903490135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185089722155404945268993423 277634583233107417903490135)
            ·
              refine ⟨416451874849661126855235203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277634583233107417903490135 416451874849661126855235203)
              ·
                refine ⟨624677812274491690282852805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416451874849661126855235203 624677812274491690282852805)
                ·
                  refine ⟨117127089801467191928034901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624677812274491690282852805 117127089801467191928034901)
                  ·
                    refine ⟨1372583083610943655406659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117127089801467191928034901 1372583083610943655406659)
                    ·
                      rfl

theorem cell22_4009644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_4009644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009644 prefixEnd_4009644 := by exact prefixLift 4009644
  have htrace : WordTrace (prefixWord ++ tailWord_4009644) baseStart_4009644 baseEnd_4009644 := by
    simpa [prefixWord, tailWord_4009644, baseEnd_4009644] using wordTrace_append hprefix tailTrace_4009644
  have hstable : (prefixWord ++ tailWord_4009644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009644).length < 2 ^ (prefixWord ++ tailWord_4009644).sum := by decide
  have hdescent : baseEnd_4009644 < baseStart_4009644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009659 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 8]
def baseStart_4009659 : Nat := 118140960795 + 4009659 * 2 ^ 59
def prefixEnd_4009659 : Nat := 4983230072969 + 3 ^ 40 * 4009659 * 2
def baseEnd_4009659 : Nat := 457529406139162872093871

theorem tailTrace_4009659 : CollatzResearch.WordTrace tailWord_4009659 prefixEnd_4009659 457529406139162872093871 := by
  unfold tailWord_4009659
  simp only [CollatzResearch.WordTrace]
  refine ⟨146244278180697713082976031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97496185453798475388650687 146244278180697713082976031)
  ·
    refine ⟨219366417271046569624464047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146244278180697713082976031 219366417271046569624464047)
    ·
      refine ⟨329049625906569854436696071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219366417271046569624464047 329049625906569854436696071)
      ·
        refine ⟨493574438859854781655044107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329049625906569854436696071 493574438859854781655044107)
        ·
          refine ⟨740361658289782172482566161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493574438859854781655044107 740361658289782172482566161)
          ·
            refine ⟨555271243717336629361924621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740361658289782172482566161 555271243717336629361924621)
            ·
              refine ⟨208226716394001236010721733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 555271243717336629361924621 208226716394001236010721733)
              ·
                refine ⟨39042509323875231752010325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208226716394001236010721733 39042509323875231752010325)
                ·
                  refine ⟨457529406139162872093871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39042509323875231752010325 457529406139162872093871)
                  ·
                    rfl

theorem cell22_4009659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 8].length) (baseStart_4009659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009659 prefixEnd_4009659 := by exact prefixLift 4009659
  have htrace : WordTrace (prefixWord ++ tailWord_4009659) baseStart_4009659 baseEnd_4009659 := by
    simpa [prefixWord, tailWord_4009659, baseEnd_4009659] using wordTrace_append hprefix tailTrace_4009659
  have hstable : (prefixWord ++ tailWord_4009659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009659).length < 2 ^ (prefixWord ++ tailWord_4009659).sum := by decide
  have hdescent : baseEnd_4009659 < baseStart_4009659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009706 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 1, 6]
def baseStart_4009706 : Nat := 118140960795 + 4009706 * 2 ^ 59
def prefixEnd_4009706 : Nat := 4983230072969 + 3 ^ 40 * 4009706 * 2
def baseEnd_4009706 : Nat := 1372604307477996160356469

theorem tailTrace_4009706 : CollatzResearch.WordTrace tailWord_4009706 prefixEnd_4009706 1372604307477996160356469 := by
  unfold tailWord_4009706
  simp only [CollatzResearch.WordTrace]
  refine ⟨36561498102881860027484243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97497328274351626739957981 36561498102881860027484243)
  ·
    refine ⟨54842247154322790041226365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36561498102881860027484243 54842247154322790041226365)
    ·
      refine ⟨20565842682871046265459887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54842247154322790041226365 20565842682871046265459887)
      ·
        refine ⟨30848764024306569398189831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20565842682871046265459887 30848764024306569398189831)
        ·
          refine ⟨46273146036459854097284747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30848764024306569398189831 46273146036459854097284747)
          ·
            refine ⟨69409719054689781145927121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46273146036459854097284747 69409719054689781145927121)
            ·
              refine ⟨52057289291017335859445341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69409719054689781145927121 52057289291017335859445341)
              ·
                refine ⟨19521483484131500947292003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52057289291017335859445341 19521483484131500947292003)
                ·
                  refine ⟨29282225226197251420938005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19521483484131500947292003 29282225226197251420938005)
                  ·
                    refine ⟨1372604307477996160356469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29282225226197251420938005 1372604307477996160356469)
                    ·
                      rfl

theorem cell22_4009706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_4009706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009706 prefixEnd_4009706 := by exact prefixLift 4009706
  have htrace : WordTrace (prefixWord ++ tailWord_4009706) baseStart_4009706 baseEnd_4009706 := by
    simpa [prefixWord, tailWord_4009706, baseEnd_4009706] using wordTrace_append hprefix tailTrace_4009706
  have hstable : (prefixWord ++ tailWord_4009706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009706).length < 2 ^ (prefixWord ++ tailWord_4009706).sum := by decide
  have hdescent : baseEnd_4009706 < baseStart_4009706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009738 : List Nat := [3, 1, 2, 2, 1, 5, 1, 7]
def baseStart_4009738 : Nat := 118140960795 + 4009738 * 2 ^ 59
def prefixEnd_4009738 : Nat := 4983230072969 + 3 ^ 40 * 4009738 * 2
def baseEnd_4009738 : Nat := 152512806859106527061819

theorem tailTrace_4009738 : CollatzResearch.WordTrace tailWord_4009738 prefixEnd_4009738 152512806859106527061819 := by
  unfold tailWord_4009738
  simp only [CollatzResearch.WordTrace]
  refine ⟨36561789886852877393775467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97498106364941006383401245 36561789886852877393775467)
  ·
    refine ⟨54842684830279316090663201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36561789886852877393775467 54842684830279316090663201)
    ·
      refine ⟨41132013622709487067997401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54842684830279316090663201 41132013622709487067997401)
      ·
        refine ⟨30849010217032115300998051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41132013622709487067997401 30849010217032115300998051)
        ·
          refine ⟨46273515325548172951497077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30849010217032115300998051 46273515325548172951497077)
          ·
            refine ⟨4338142061770141214202851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46273515325548172951497077 4338142061770141214202851)
            ·
              refine ⟨6507213092655211821304277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4338142061770141214202851 6507213092655211821304277)
              ·
                refine ⟨152512806859106527061819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6507213092655211821304277 152512806859106527061819)
                ·
                  rfl

theorem cell22_4009738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 7].length) (baseStart_4009738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009738 prefixEnd_4009738 := by exact prefixLift 4009738
  have htrace : WordTrace (prefixWord ++ tailWord_4009738) baseStart_4009738 baseEnd_4009738 := by
    simpa [prefixWord, tailWord_4009738, baseEnd_4009738] using wordTrace_append hprefix tailTrace_4009738
  have hstable : (prefixWord ++ tailWord_4009738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009738).length < 2 ^ (prefixWord ++ tailWord_4009738).sum := by decide
  have hdescent : baseEnd_4009738 < baseStart_4009738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009800 : List Nat := [2, 1, 3, 1, 1, 5, 3, 1, 5]
def baseStart_4009800 : Nat := 118140960795 + 4009800 * 2 ^ 59
def prefixEnd_4009800 : Nat := 4983230072969 + 3 ^ 40 * 4009800 * 2
def baseEnd_4009800 : Nat := 457545495199670416168727

theorem tailTrace_4009800 : CollatzResearch.WordTrace tailWord_4009800 prefixEnd_4009800 457545495199670416168727 := by
  unfold tailWord_4009800
  simp only [CollatzResearch.WordTrace]
  refine ⟨73124710436593447081929427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97499613915457929442572569 73124710436593447081929427)
  ·
    refine ⟨109687065654890170622894141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73124710436593447081929427 109687065654890170622894141)
    ·
      refine ⟨41132649620583813983585303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109687065654890170622894141 41132649620583813983585303)
      ·
        refine ⟨61698974430875720975377955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41132649620583813983585303 61698974430875720975377955)
        ·
          refine ⟨92548461646313581463066933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61698974430875720975377955 92548461646313581463066933)
          ·
            refine ⟨8676418279341898262162525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92548461646313581463066933 8676418279341898262162525)
            ·
              refine ⟨3253656854753211848310947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8676418279341898262162525 3253656854753211848310947)
              ·
                refine ⟨4880485282129817772466421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3253656854753211848310947 4880485282129817772466421)
                ·
                  refine ⟨457545495199670416168727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4880485282129817772466421 457545495199670416168727)
                  ·
                    rfl

theorem cell22_4009800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 5].length) (baseStart_4009800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009800 prefixEnd_4009800 := by exact prefixLift 4009800
  have htrace : WordTrace (prefixWord ++ tailWord_4009800) baseStart_4009800 baseEnd_4009800 := by
    simpa [prefixWord, tailWord_4009800, baseEnd_4009800] using wordTrace_append hprefix tailTrace_4009800
  have hstable : (prefixWord ++ tailWord_4009800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009800).length < 2 ^ (prefixWord ++ tailWord_4009800).sum := by decide
  have hdescent : baseEnd_4009800 < baseStart_4009800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009864 : List Nat := [2, 1, 3, 3, 4, 1, 1, 2, 1, 4]
def baseStart_4009864 : Nat := 118140960795 + 4009864 * 2 ^ 59
def prefixEnd_4009864 : Nat := 4983230072969 + 3 ^ 40 * 4009864 * 2
def baseEnd_4009864 : Nat := 1372658394106936414905985

theorem tailTrace_4009864 : CollatzResearch.WordTrace tailWord_4009864 prefixEnd_4009864 1372658394106936414905985 := by
  unfold tailWord_4009864
  simp only [CollatzResearch.WordTrace]
  refine ⟨73125877572477516547094323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97501170096636688729459097 73125877572477516547094323)
  ·
    refine ⟨109688816358716274820641485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73125877572477516547094323 109688816358716274820641485)
    ·
      refine ⟨41133306134518603057740557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109688816358716274820641485 41133306134518603057740557)
      ·
        refine ⟨15424989800444476146652709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41133306134518603057740557 15424989800444476146652709)
        ·
          refine ⟨2892185587583339277497383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15424989800444476146652709 2892185587583339277497383)
          ·
            refine ⟨4338278381375008916246075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2892185587583339277497383 4338278381375008916246075)
            ·
              refine ⟨6507417572062513374369113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4338278381375008916246075 6507417572062513374369113)
              ·
                refine ⟨4880563179046885030776835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6507417572062513374369113 4880563179046885030776835)
                ·
                  refine ⟨7320844768570327546165253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4880563179046885030776835 7320844768570327546165253)
                  ·
                    refine ⟨1372658394106936414905985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7320844768570327546165253 1372658394106936414905985)
                    ·
                      rfl

theorem cell22_4009864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_4009864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009864 prefixEnd_4009864 := by exact prefixLift 4009864
  have htrace : WordTrace (prefixWord ++ tailWord_4009864) baseStart_4009864 baseEnd_4009864 := by
    simpa [prefixWord, tailWord_4009864, baseEnd_4009864] using wordTrace_append hprefix tailTrace_4009864
  have hstable : (prefixWord ++ tailWord_4009864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009864).length < 2 ^ (prefixWord ++ tailWord_4009864).sum := by decide
  have hdescent : baseEnd_4009864 < baseStart_4009864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009890 : List Nat := [3, 3, 1, 2, 4, 9]
def baseStart_4009890 : Nat := 118140960795 + 4009890 * 2 ^ 59
def prefixEnd_4009890 : Nat := 4983230072969 + 3 ^ 40 * 4009890 * 2
def baseEnd_4009890 : Nat := 16946509807880012515505

theorem tailTrace_4009890 : CollatzResearch.WordTrace tailWord_4009890 prefixEnd_4009890 16946509807880012515505 := by
  unfold tailWord_4009890
  simp only [CollatzResearch.WordTrace]
  refine ⟨36563175860715209883658781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97501802295240559689756749 36563175860715209883658781)
  ·
    refine ⟨13711190947768203706372043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36563175860715209883658781 13711190947768203706372043)
    ·
      refine ⟨20566786421652305559558065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13711190947768203706372043 20566786421652305559558065)
      ·
        refine ⟨15425089816239229169668549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20566786421652305559558065 15425089816239229169668549)
        ·
          refine ⟨2892204340544855469312853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15425089816239229169668549 2892204340544855469312853)
          ·
            refine ⟨16946509807880012515505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2892204340544855469312853 16946509807880012515505)
            ·
              rfl

theorem cell22_4009890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 9].length) (baseStart_4009890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009890 prefixEnd_4009890 := by exact prefixLift 4009890
  have htrace : WordTrace (prefixWord ++ tailWord_4009890) baseStart_4009890 baseEnd_4009890 := by
    simpa [prefixWord, tailWord_4009890, baseEnd_4009890] using wordTrace_append hprefix tailTrace_4009890
  have hstable : (prefixWord ++ tailWord_4009890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009890).length < 2 ^ (prefixWord ++ tailWord_4009890).sum := by decide
  have hdescent : baseEnd_4009890 < baseStart_4009890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009995 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 6, 3]
def baseStart_4009995 : Nat := 118140960795 + 4009995 * 2 ^ 59
def prefixEnd_4009995 : Nat := 4983230072969 + 3 ^ 40 * 4009995 * 2
def baseEnd_4009995 : Nat := 1372703238084095739880583

theorem tailTrace_4009995 : CollatzResearch.WordTrace tailWord_4009995 prefixEnd_4009995 1372703238084095739880583 := by
  unfold tailWord_4009995
  simp only [CollatzResearch.WordTrace]
  refine ⟨146256533107480442467207439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97504355404986961644804959 146256533107480442467207439)
  ·
    refine ⟨219384799661220663700811159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146256533107480442467207439 219384799661220663700811159)
    ·
      refine ⟨329077199491830995551216739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219384799661220663700811159 329077199491830995551216739)
      ·
        refine ⟨493615799237746493326825109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329077199491830995551216739 493615799237746493326825109)
        ·
          refine ⟨23138240589269366874694927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 493615799237746493326825109 23138240589269366874694927)
          ·
            refine ⟨34707360883904050312042391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23138240589269366874694927 34707360883904050312042391)
            ·
              refine ⟨52061041325856075468063587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34707360883904050312042391 52061041325856075468063587)
              ·
                refine ⟨78091561988784113202095381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52061041325856075468063587 78091561988784113202095381)
                ·
                  refine ⟨3660541968224255306348221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78091561988784113202095381 3660541968224255306348221)
                  ·
                    refine ⟨1372703238084095739880583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3660541968224255306348221 1372703238084095739880583)
                    ·
                      rfl

theorem cell22_4009995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 3].length) (baseStart_4009995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4009995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4009995 prefixEnd_4009995 := by exact prefixLift 4009995
  have htrace : WordTrace (prefixWord ++ tailWord_4009995) baseStart_4009995 baseEnd_4009995 := by
    simpa [prefixWord, tailWord_4009995, baseEnd_4009995] using wordTrace_append hprefix tailTrace_4009995
  have hstable : (prefixWord ++ tailWord_4009995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009995).length < 2 ^ (prefixWord ++ tailWord_4009995).sum := by decide
  have hdescent : baseEnd_4009995 < baseStart_4009995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010010 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 4, 4]
def baseStart_4010010 : Nat := 118140960795 + 4010010 * 2 ^ 59
def prefixEnd_4010010 : Nat := 4983230072969 + 3 ^ 40 * 4010010 * 2
def baseEnd_4010010 : Nat := 1372708372890640700755537

theorem tailTrace_4010010 : CollatzResearch.WordTrace tailWord_4010010 prefixEnd_4010010 1372708372890640700755537 := by
  unfold tailWord_4010010
  simp only [CollatzResearch.WordTrace]
  refine ⟨36564270050606525007250871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97504720134950733352668989 36564270050606525007250871)
  ·
    refine ⟨54846405075909787510876307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36564270050606525007250871 54846405075909787510876307)
    ·
      refine ⟨82269607613864681266314461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54846405075909787510876307 82269607613864681266314461)
      ·
        refine ⟨30851102855199255474867923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82269607613864681266314461 30851102855199255474867923)
        ·
          refine ⟨46276654282798883212301885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30851102855199255474867923 46276654282798883212301885)
          ·
            refine ⟨17353745356049581204613207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46276654282798883212301885 17353745356049581204613207)
            ·
              refine ⟨26030618034074371806919811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17353745356049581204613207 26030618034074371806919811)
              ·
                refine ⟨39045927051111557710379717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26030618034074371806919811 39045927051111557710379717)
                ·
                  refine ⟨7321111322083417070696197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39045927051111557710379717 7321111322083417070696197)
                  ·
                    refine ⟨1372708372890640700755537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7321111322083417070696197 1372708372890640700755537)
                    ·
                      rfl

theorem cell22_4010010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_4010010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010010 prefixEnd_4010010 := by exact prefixLift 4010010
  have htrace : WordTrace (prefixWord ++ tailWord_4010010) baseStart_4010010 baseEnd_4010010 := by
    simpa [prefixWord, tailWord_4010010, baseEnd_4010010] using wordTrace_append hprefix tailTrace_4010010
  have hstable : (prefixWord ++ tailWord_4010010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010010).length < 2 ^ (prefixWord ++ tailWord_4010010).sum := by decide
  have hdescent : baseEnd_4010010 < baseStart_4010010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010012 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 4, 3]
def baseStart_4010012 : Nat := 118140960795 + 4010012 * 2 ^ 59
def prefixEnd_4010012 : Nat := 4983230072969 + 3 ^ 40 * 4010012 * 2
def baseEnd_4010012 : Nat := 1372709057531513362205531

theorem tailTrace_4010012 : CollatzResearch.WordTrace tailWord_4010012 prefixEnd_4010012 1372709057531513362205531 := by
  unfold tailWord_4010012
  simp only [CollatzResearch.WordTrace]
  refine ⟨73128576574209427185288145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97504768765612569580384193 73128576574209427185288145)
  ·
    refine ⟨54846432430657070388966109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73128576574209427185288145 54846432430657070388966109)
    ·
      refine ⟨20567412161496401395862291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54846432430657070388966109 20567412161496401395862291)
      ·
        refine ⟨30851118242244602093793437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20567412161496401395862291 30851118242244602093793437)
        ·
          refine ⟨11569169340841725785172539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30851118242244602093793437 11569169340841725785172539)
          ·
            refine ⟨17353754011262588677758809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11569169340841725785172539 17353754011262588677758809)
            ·
              refine ⟨13015315508446941508319107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17353754011262588677758809 13015315508446941508319107)
              ·
                refine ⟨19522973262670412262478661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13015315508446941508319107 19522973262670412262478661)
                ·
                  refine ⟨3660557486750702299214749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19522973262670412262478661 3660557486750702299214749)
                  ·
                    refine ⟨1372709057531513362205531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3660557486750702299214749 1372709057531513362205531)
                    ·
                      rfl

theorem cell22_4010012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_4010012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010012 prefixEnd_4010012 := by exact prefixLift 4010012
  have htrace : WordTrace (prefixWord ++ tailWord_4010012) baseStart_4010012 baseEnd_4010012 := by
    simpa [prefixWord, tailWord_4010012, baseEnd_4010012] using wordTrace_append hprefix tailTrace_4010012
  have hstable : (prefixWord ++ tailWord_4010012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010012).length < 2 ^ (prefixWord ++ tailWord_4010012).sum := by decide
  have hdescent : baseEnd_4010012 < baseStart_4010012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010074 : List Nat := [3, 1, 1, 2, 1, 1, 5, 4, 1, 3]
def baseStart_4010074 : Nat := 118140960795 + 4010074 * 2 ^ 59
def prefixEnd_4010074 : Nat := 4983230072969 + 3 ^ 40 * 4010074 * 2
def baseEnd_4010074 : Nat := 1372730281398565867155341

theorem tailTrace_4010074 : CollatzResearch.WordTrace tailWord_4010074 prefixEnd_4010074 1372730281398565867155341 := by
  unfold tailWord_4010074
  simp only [CollatzResearch.WordTrace]
  refine ⟨36564853618548559739833319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97506276316129492639555517 36564853618548559739833319)
  ·
    refine ⟨54847280427822839609749979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36564853618548559739833319 54847280427822839609749979)
    ·
      refine ⟨82270920641734259414624969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54847280427822839609749979 82270920641734259414624969)
      ·
        refine ⟨61703190481300694560968727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82270920641734259414624969 61703190481300694560968727)
        ·
          refine ⟨92554785721951041841453091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61703190481300694560968727 92554785721951041841453091)
          ·
            refine ⟨138832178582926562762179637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92554785721951041841453091 138832178582926562762179637)
            ·
              refine ⟨13015516742149365258954341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138832178582926562762179637 13015516742149365258954341)
              ·
                refine ⟨2440409389153005986053939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13015516742149365258954341 2440409389153005986053939)
                ·
                  refine ⟨3660614083729508979080909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2440409389153005986053939 3660614083729508979080909)
                  ·
                    refine ⟨1372730281398565867155341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3660614083729508979080909 1372730281398565867155341)
                    ·
                      rfl

theorem cell22_4010074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 1, 3].length) (baseStart_4010074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010074 prefixEnd_4010074 := by exact prefixLift 4010074
  have htrace : WordTrace (prefixWord ++ tailWord_4010074) baseStart_4010074 baseEnd_4010074 := by
    simpa [prefixWord, tailWord_4010074, baseEnd_4010074] using wordTrace_append hprefix tailTrace_4010074
  have hstable : (prefixWord ++ tailWord_4010074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010074).length < 2 ^ (prefixWord ++ tailWord_4010074).sum := by decide
  have hdescent : baseEnd_4010074 < baseStart_4010074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010085 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 1, 7]
def baseStart_4010085 : Nat := 118140960795 + 4010085 * 2 ^ 59
def prefixEnd_4010085 : Nat := 4983230072969 + 3 ^ 40 * 4010085 * 2
def baseEnd_4010085 : Nat := 1372734046923365505130307

theorem tailTrace_4010085 : CollatzResearch.WordTrace tailWord_4010085 prefixEnd_4010085 1372734046923365505130307 := by
  unfold tailWord_4010085
  simp only [CollatzResearch.WordTrace]
  refine ⟨146259815677154387837983709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97506543784769591891989139 146259815677154387837983709)
  ·
    refine ⟨54847430878932895439243891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146259815677154387837983709 54847430878932895439243891)
    ·
      refine ⟨82271146318399343158865837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54847430878932895439243891 82271146318399343158865837)
      ·
        refine ⟨30851679869399753684574689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82271146318399343158865837 30851679869399753684574689)
        ·
          refine ⟨23138759902049815263431017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30851679869399753684574689 23138759902049815263431017)
          ·
            refine ⟨17354069926537361447573263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23138759902049815263431017 17354069926537361447573263)
            ·
              refine ⟨26031104889806042171359895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17354069926537361447573263 26031104889806042171359895)
              ·
                refine ⟨39046657334709063257039843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26031104889806042171359895 39046657334709063257039843)
                ·
                  refine ⟨58569986002063594885559765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39046657334709063257039843 58569986002063594885559765)
                  ·
                    refine ⟨1372734046923365505130307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58569986002063594885559765 1372734046923365505130307)
                    ·
                      rfl

theorem cell22_4010085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_4010085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010085 prefixEnd_4010085 := by exact prefixLift 4010085
  have htrace : WordTrace (prefixWord ++ tailWord_4010085) baseStart_4010085 baseEnd_4010085 := by
    simpa [prefixWord, tailWord_4010085, baseEnd_4010085] using wordTrace_append hprefix tailTrace_4010085
  have hstable : (prefixWord ++ tailWord_4010085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010085).length < 2 ^ (prefixWord ++ tailWord_4010085).sum := by decide
  have hdescent : baseEnd_4010085 < baseStart_4010085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010151 : List Nat := [1, 1, 6, 2, 2, 1, 2, 2, 1, 4]
def baseStart_4010151 : Nat := 118140960795 + 4010151 * 2 ^ 59
def prefixEnd_4010151 : Nat := 4983230072969 + 3 ^ 40 * 4010151 * 2
def baseEnd_4010151 : Nat := 1372756640072163332980105

theorem tailTrace_4010151 : CollatzResearch.WordTrace tailWord_4010151 prefixEnd_4010151 1372756640072163332980105 := by
  unfold tailWord_4010151
  simp only [CollatzResearch.WordTrace]
  refine ⟨146262222894915281109886307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97508148596610187406590871 146262222894915281109886307)
  ·
    refine ⟨219393334342372921664829461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146262222894915281109886307 219393334342372921664829461)
    ·
      refine ⟨10284062547298730703038881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 219393334342372921664829461 10284062547298730703038881)
      ·
        refine ⟨7713046910474048027279161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10284062547298730703038881 7713046910474048027279161)
        ·
          refine ⟨5784785182855536020459371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7713046910474048027279161 5784785182855536020459371)
          ·
            refine ⟨8677177774283304030689057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5784785182855536020459371 8677177774283304030689057)
            ·
              refine ⟨6507883330712478023016793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8677177774283304030689057 6507883330712478023016793)
              ·
                refine ⟨4880912498034358517262595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6507883330712478023016793 4880912498034358517262595)
                ·
                  refine ⟨7321368747051537775893893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4880912498034358517262595 7321368747051537775893893)
                  ·
                    refine ⟨1372756640072163332980105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7321368747051537775893893 1372756640072163332980105)
                    ·
                      rfl

theorem cell22_4010151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_4010151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010151 prefixEnd_4010151 := by exact prefixLift 4010151
  have htrace : WordTrace (prefixWord ++ tailWord_4010151) baseStart_4010151 baseEnd_4010151 := by
    simpa [prefixWord, tailWord_4010151, baseEnd_4010151] using wordTrace_append hprefix tailTrace_4010151
  have hstable : (prefixWord ++ tailWord_4010151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010151).length < 2 ^ (prefixWord ++ tailWord_4010151).sum := by decide
  have hdescent : baseEnd_4010151 < baseStart_4010151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010162 : List Nat := [3, 2, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_4010162 : Nat := 118140960795 + 4010162 * 2 ^ 59
def prefixEnd_4010162 : Nat := 4983230072969 + 3 ^ 40 * 4010162 * 2
def baseEnd_4010162 : Nat := 1372760405596962970955071

theorem tailTrace_4010162 : CollatzResearch.WordTrace tailWord_4010162 prefixEnd_4010162 1372760405596962970955071 := by
  unfold tailWord_4010162
  simp only [CollatzResearch.WordTrace]
  refine ⟨36565656024468857497134185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97508416065250286659024493 36565656024468857497134185)
  ·
    refine ⟨27424242018351643122850639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36565656024468857497134185 27424242018351643122850639)
    ·
      refine ⟨41136363027527464684275959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27424242018351643122850639 41136363027527464684275959)
      ·
        refine ⟨61704544541291197026413939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41136363027527464684275959 61704544541291197026413939)
        ·
          refine ⟨92556816811936795539620909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61704544541291197026413939 92556816811936795539620909)
          ·
            refine ⟨34708806304476298327357841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92556816811936795539620909 34708806304476298327357841)
            ·
              refine ⟨26031604728357223745518381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34708806304476298327357841 26031604728357223745518381)
              ·
                refine ⟨9761851773133958904569393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26031604728357223745518381 9761851773133958904569393)
                ·
                  refine ⟨7321388829850469178427045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9761851773133958904569393 7321388829850469178427045)
                  ·
                    refine ⟨1372760405596962970955071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7321388829850469178427045 1372760405596962970955071)
                    ·
                      rfl

theorem cell22_4010162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_4010162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010162 prefixEnd_4010162 := by exact prefixLift 4010162
  have htrace : WordTrace (prefixWord ++ tailWord_4010162) baseStart_4010162 baseEnd_4010162 := by
    simpa [prefixWord, tailWord_4010162, baseEnd_4010162] using wordTrace_append hprefix tailTrace_4010162
  have hstable : (prefixWord ++ tailWord_4010162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010162).length < 2 ^ (prefixWord ++ tailWord_4010162).sum := by decide
  have hdescent : baseEnd_4010162 < baseStart_4010162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010198 : List Nat := [5, 2, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_4010198 : Nat := 118140960795 + 4010198 * 2 ^ 59
def prefixEnd_4010198 : Nat := 4983230072969 + 3 ^ 40 * 4010198 * 2
def baseEnd_4010198 : Nat := 1372772729132670877054961

theorem tailTrace_4010198 : CollatzResearch.WordTrace tailWord_4010198 prefixEnd_4010198 1372772729132670877054961 := by
  unfold tailWord_4010198
  simp only [CollatzResearch.WordTrace]
  refine ⟨9141496070359063008552953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97509291417163338757898165 9141496070359063008552953)
  ·
    refine ⟨6856122052769297256414715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9141496070359063008552953 6856122052769297256414715)
    ·
      refine ⟨10284183079153945884622073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6856122052769297256414715 10284183079153945884622073)
      ·
        refine ⟨7713137309365459413466555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10284183079153945884622073 7713137309365459413466555)
        ·
          refine ⟨11569705964048189120199833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7713137309365459413466555 11569705964048189120199833)
          ·
            refine ⟨8677279473036141840149875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11569705964048189120199833 8677279473036141840149875)
            ·
              refine ⟨13015919209554212760224813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8677279473036141840149875 13015919209554212760224813)
              ·
                refine ⟨4880969703582829785084305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13015919209554212760224813 4880969703582829785084305)
                ·
                  refine ⟨3660727277687122338813229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4880969703582829785084305 3660727277687122338813229)
                  ·
                    refine ⟨1372772729132670877054961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3660727277687122338813229 1372772729132670877054961)
                    ·
                      rfl

theorem cell22_4010198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_4010198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010198 prefixEnd_4010198 := by exact prefixLift 4010198
  have htrace : WordTrace (prefixWord ++ tailWord_4010198) baseStart_4010198 baseEnd_4010198 := by
    simpa [prefixWord, tailWord_4010198, baseEnd_4010198] using wordTrace_append hprefix tailTrace_4010198
  have hstable : (prefixWord ++ tailWord_4010198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010198).length < 2 ^ (prefixWord ++ tailWord_4010198).sum := by decide
  have hdescent : baseEnd_4010198 < baseStart_4010198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010252 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 5, 4]
def baseStart_4010252 : Nat := 118140960795 + 4010252 * 2 ^ 59
def prefixEnd_4010252 : Nat := 4983230072969 + 3 ^ 40 * 4010252 * 2
def baseEnd_4010252 : Nat := 1372791214436232736204795

theorem tailTrace_4010252 : CollatzResearch.WordTrace tailWord_4010252 prefixEnd_4010252 1372791214436232736204795 := by
  unfold tailWord_4010252
  simp only [CollatzResearch.WordTrace]
  refine ⟨73132953333774687679656505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97510604445032916906208673 73132953333774687679656505)
  ·
    refine ⟨54849715000331015759742379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73132953333774687679656505 54849715000331015759742379)
    ·
      refine ⟨82274572500496523639613569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54849715000331015759742379 82274572500496523639613569)
      ·
        refine ⟨61705929375372392729710177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82274572500496523639613569 61705929375372392729710177)
        ·
          refine ⟨46279447031529294547282633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61705929375372392729710177 46279447031529294547282633)
          ·
            refine ⟨34709585273646970910461975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46279447031529294547282633 34709585273646970910461975)
            ·
              refine ⟨52064377910470456365692963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34709585273646970910461975 52064377910470456365692963)
              ·
                refine ⟨78096566865705684548539445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52064377910470456365692963 78096566865705684548539445)
                ·
                  refine ⟨7321553143659907926425573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78096566865705684548539445 7321553143659907926425573)
                  ·
                    refine ⟨1372791214436232736204795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7321553143659907926425573 1372791214436232736204795)
                    ·
                      rfl

theorem cell22_4010252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_4010252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010252 prefixEnd_4010252 := by exact prefixLift 4010252
  have htrace : WordTrace (prefixWord ++ tailWord_4010252) baseStart_4010252 baseEnd_4010252 := by
    simpa [prefixWord, tailWord_4010252, baseEnd_4010252] using wordTrace_append hprefix tailTrace_4010252
  have hstable : (prefixWord ++ tailWord_4010252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010252).length < 2 ^ (prefixWord ++ tailWord_4010252).sum := by decide
  have hdescent : baseEnd_4010252 < baseStart_4010252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010284 : List Nat := [2, 2, 1, 1, 1, 3, 3, 5, 4]
def baseStart_4010284 : Nat := 118140960795 + 4010284 * 2 ^ 59
def prefixEnd_4010284 : Nat := 4983230072969 + 3 ^ 40 * 4010284 * 2
def baseEnd_4010284 : Nat := 457600722896731773134899

theorem tailTrace_4010284 : CollatzResearch.WordTrace tailWord_4010284 prefixEnd_4010284 457600722896731773134899 := by
  unfold tailWord_4010284
  simp only [CollatzResearch.WordTrace]
  refine ⟨73133536901716722412238953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97511382535622296549651937 73133536901716722412238953)
  ·
    refine ⟨54850152676287541809179215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73133536901716722412238953 54850152676287541809179215)
    ·
      refine ⟨82275229014431312713768823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54850152676287541809179215 82275229014431312713768823)
      ·
        refine ⟨123412843521646969070653235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82275229014431312713768823 123412843521646969070653235)
        ·
          refine ⟨185119265282470453605979853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123412843521646969070653235 185119265282470453605979853)
          ·
            refine ⟨69419724480926420102242445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185119265282470453605979853 69419724480926420102242445)
            ·
              refine ⟨26032396680347407538340917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69419724480926420102242445 26032396680347407538340917)
              ·
                refine ⟨2440537188782569456719461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26032396680347407538340917 2440537188782569456719461)
                ·
                  refine ⟨457600722896731773134899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2440537188782569456719461 457600722896731773134899)
                  ·
                    rfl

theorem cell22_4010284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_4010284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010284 prefixEnd_4010284 := by exact prefixLift 4010284
  have htrace : WordTrace (prefixWord ++ tailWord_4010284) baseStart_4010284 baseEnd_4010284 := by
    simpa [prefixWord, tailWord_4010284, baseEnd_4010284] using wordTrace_append hprefix tailTrace_4010284
  have hstable : (prefixWord ++ tailWord_4010284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010284).length < 2 ^ (prefixWord ++ tailWord_4010284).sum := by decide
  have hdescent : baseEnd_4010284 < baseStart_4010284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010327 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 2, 7]
def baseStart_4010327 : Nat := 118140960795 + 4010327 * 2 ^ 59
def prefixEnd_4010327 : Nat := 4983230072969 + 3 ^ 40 * 4010327 * 2
def baseEnd_4010327 : Nat := 1372816888468957540579565

theorem tailTrace_4010327 : CollatzResearch.WordTrace tailWord_4010327 prefixEnd_4010327 1372816888468957540579565 := by
  unfold tailWord_4010327
  simp only [CollatzResearch.WordTrace]
  refine ⟨146268642142277663168293235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97512428094851775445528823 146268642142277663168293235)
  ·
    refine ⟨219402963213416494752439853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146268642142277663168293235 219402963213416494752439853)
    ·
      refine ⟨82276111205031185532164945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219402963213416494752439853 82276111205031185532164945)
      ·
        refine ⟨61707083403773389149123709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82276111205031185532164945 61707083403773389149123709)
        ·
          refine ⟨23140156276415020930921391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61707083403773389149123709 23140156276415020930921391)
          ·
            refine ⟨34710234414622531396382087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23140156276415020930921391 34710234414622531396382087)
            ·
              refine ⟨52065351621933797094573131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34710234414622531396382087 52065351621933797094573131)
              ·
                refine ⟨78098027432900695641859697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52065351621933797094573131 78098027432900695641859697)
                ·
                  refine ⟨58573520574675521731394773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78098027432900695641859697 58573520574675521731394773)
                  ·
                    refine ⟨1372816888468957540579565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58573520574675521731394773 1372816888468957540579565)
                    ·
                      rfl

theorem cell22_4010327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_4010327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010327 prefixEnd_4010327 := by exact prefixLift 4010327
  have htrace : WordTrace (prefixWord ++ tailWord_4010327) baseStart_4010327 baseEnd_4010327 := by
    simpa [prefixWord, tailWord_4010327, baseEnd_4010327] using wordTrace_append hprefix tailTrace_4010327
  have hstable : (prefixWord ++ tailWord_4010327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010327).length < 2 ^ (prefixWord ++ tailWord_4010327).sum := by decide
  have hdescent : baseEnd_4010327 < baseStart_4010327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010408 : List Nat := [2, 1, 6, 1, 1, 2, 2, 2, 5]
def baseStart_4010408 : Nat := 118140960795 + 4010408 * 2 ^ 59
def prefixEnd_4010408 : Nat := 4983230072969 + 3 ^ 40 * 4010408 * 2
def baseEnd_4010408 : Nat := 457614872141433443101439

theorem tailTrace_4010408 : CollatzResearch.WordTrace tailWord_4010408 prefixEnd_4010408 457614872141433443101439 := by
  unfold tailWord_4010408
  simp only [CollatzResearch.WordTrace]
  refine ⟨73135798227492107000995939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97514397636656142667994585 73135798227492107000995939)
  ·
    refine ⟨109703697341238160501493909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73135798227492107000995939 109703697341238160501493909)
    ·
      refine ⟨5142360812870538773507527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109703697341238160501493909 5142360812870538773507527)
      ·
        refine ⟨7713541219305808160261291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5142360812870538773507527 7713541219305808160261291)
        ·
          refine ⟨11570311828958712240391937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7713541219305808160261291 11570311828958712240391937)
          ·
            refine ⟨8677733871719034180293953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11570311828958712240391937 8677733871719034180293953)
            ·
              refine ⟨6508300403789275635220465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8677733871719034180293953 6508300403789275635220465)
              ·
                refine ⟨4881225302841956726415349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6508300403789275635220465 4881225302841956726415349)
                ·
                  refine ⟨457614872141433443101439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4881225302841956726415349 457614872141433443101439)
                  ·
                    rfl

theorem cell22_4010408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 5].length) (baseStart_4010408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010408 prefixEnd_4010408 := by exact prefixLift 4010408
  have htrace : WordTrace (prefixWord ++ tailWord_4010408) baseStart_4010408 baseEnd_4010408 := by
    simpa [prefixWord, tailWord_4010408, baseEnd_4010408] using wordTrace_append hprefix tailTrace_4010408
  have hstable : (prefixWord ++ tailWord_4010408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010408).length < 2 ^ (prefixWord ++ tailWord_4010408).sum := by decide
  have hdescent : baseEnd_4010408 < baseStart_4010408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010453 : List Nat := [1, 3, 2, 3, 1, 3, 2, 3, 4]
def baseStart_4010453 : Nat := 118140960795 + 4010453 * 2 ^ 59
def prefixEnd_4010453 : Nat := 4983230072969 + 3 ^ 40 * 4010453 * 2
def baseEnd_4010453 : Nat := 457620006947978403976393

theorem tailTrace_4010453 : CollatzResearch.WordTrace tailWord_4010453 prefixEnd_4010453 457620006947978403976393 := by
  unfold tailWord_4010453
  simp only [CollatzResearch.WordTrace]
  refine ⟨146273237739821186687380013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97515491826547457791586675 146273237739821186687380013)
  ·
    refine ⟨54852464152432945007767505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146273237739821186687380013 54852464152432945007767505)
    ·
      refine ⟨41139348114324708755825629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54852464152432945007767505 41139348114324708755825629)
      ·
        refine ⟨15427255542871765783434611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41139348114324708755825629 15427255542871765783434611)
        ·
          refine ⟨23140883314307648675151917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15427255542871765783434611 23140883314307648675151917)
          ·
            refine ⟨8677831242865368253181969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23140883314307648675151917 8677831242865368253181969)
            ·
              refine ⟨6508373432149026189886477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8677831242865368253181969 6508373432149026189886477)
              ·
                refine ⟨2440640037055884821207429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6508373432149026189886477 2440640037055884821207429)
                ·
                  refine ⟨457620006947978403976393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2440640037055884821207429 457620006947978403976393)
                  ·
                    rfl

theorem cell22_4010453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_4010453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010453 prefixEnd_4010453 := by exact prefixLift 4010453
  have htrace : WordTrace (prefixWord ++ tailWord_4010453) baseStart_4010453 baseEnd_4010453 := by
    simpa [prefixWord, tailWord_4010453, baseEnd_4010453] using wordTrace_append hprefix tailTrace_4010453
  have hstable : (prefixWord ++ tailWord_4010453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010453).length < 2 ^ (prefixWord ++ tailWord_4010453).sum := by decide
  have hdescent : baseEnd_4010453 < baseStart_4010453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010485 : List Nat := [1, 3, 5, 1, 2, 2, 1, 1, 1, 5]
def baseStart_4010485 : Nat := 118140960795 + 4010485 * 2 ^ 59
def prefixEnd_4010485 : Nat := 4983230072969 + 3 ^ 40 * 4010485 * 2
def baseEnd_4010485 : Nat := 1372870975097897795129081

theorem tailTrace_4010485 : CollatzResearch.WordTrace tailWord_4010485 prefixEnd_4010485 1372870975097897795129081 := by
  unfold tailWord_4010485
  simp only [CollatzResearch.WordTrace]
  refine ⟨146274404875705256152544909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97516269917136837435029939 146274404875705256152544909)
  ·
    refine ⟨54852901828389471057204341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146274404875705256152544909 54852901828389471057204341)
    ·
      refine ⟨5142459546411512911612907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54852901828389471057204341 5142459546411512911612907)
      ·
        refine ⟨7713689319617269367419361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5142459546411512911612907 7713689319617269367419361)
        ·
          refine ⟨5785266989712952025564521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7713689319617269367419361 5785266989712952025564521)
          ·
            refine ⟨4338950242284714019173391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5785266989712952025564521 4338950242284714019173391)
            ·
              refine ⟨6508425363427071028760087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4338950242284714019173391 6508425363427071028760087)
              ·
                refine ⟨9762638045140606543140131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6508425363427071028760087 9762638045140606543140131)
                ·
                  refine ⟨14643957067710909814710197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9762638045140606543140131 14643957067710909814710197)
                  ·
                    refine ⟨1372870975097897795129081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14643957067710909814710197 1372870975097897795129081)
                    ·
                      rfl

theorem cell22_4010485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_4010485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010485 prefixEnd_4010485 := by exact prefixLift 4010485
  have htrace : WordTrace (prefixWord ++ tailWord_4010485) baseStart_4010485 baseEnd_4010485 := by
    simpa [prefixWord, tailWord_4010485, baseEnd_4010485] using wordTrace_append hprefix tailTrace_4010485
  have hstable : (prefixWord ++ tailWord_4010485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010485).length < 2 ^ (prefixWord ++ tailWord_4010485).sum := by decide
  have hdescent : baseEnd_4010485 < baseStart_4010485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010498 : List Nat := [3, 4, 1, 2, 2, 1, 1, 8]
def baseStart_4010498 : Nat := 118140960795 + 4010498 * 2 ^ 59
def prefixEnd_4010498 : Nat := 4983230072969 + 3 ^ 40 * 4010498 * 2
def baseEnd_4010498 : Nat := 152541713918174454950449

theorem tailTrace_4010498 : CollatzResearch.WordTrace tailWord_4010498 prefixEnd_4010498 152541713918174454950449 := by
  unfold tailWord_4010498
  simp only [CollatzResearch.WordTrace]
  refine ⟨36568719756164539843192037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97516586016438772915178765 36568719756164539843192037)
  ·
    refine ⟨6856634954280851220598507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36568719756164539843192037 6856634954280851220598507)
    ·
      refine ⟨10284952431421276830897761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6856634954280851220598507 10284952431421276830897761)
      ·
        refine ⟨7713714323565957623173321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10284952431421276830897761 7713714323565957623173321)
        ·
          refine ⟨5785285742674468217379991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7713714323565957623173321 5785285742674468217379991)
          ·
            refine ⟨8677928614011702326069987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5785285742674468217379991 8677928614011702326069987)
            ·
              refine ⟨13016892921017553489104981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8677928614011702326069987 13016892921017553489104981)
              ·
                refine ⟨152541713918174454950449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13016892921017553489104981 152541713918174454950449)
                ·
                  rfl

theorem cell22_4010498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 8].length) (baseStart_4010498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010498 prefixEnd_4010498 := by exact prefixLift 4010498
  have htrace : WordTrace (prefixWord ++ tailWord_4010498) baseStart_4010498 baseEnd_4010498 := by
    simpa [prefixWord, tailWord_4010498, baseEnd_4010498] using wordTrace_append hprefix tailTrace_4010498
  have hstable : (prefixWord ++ tailWord_4010498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010498).length < 2 ^ (prefixWord ++ tailWord_4010498).sum := by decide
  have hdescent : baseEnd_4010498 < baseStart_4010498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
