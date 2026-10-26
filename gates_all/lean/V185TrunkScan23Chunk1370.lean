import V185TrunkScan23Chunk1369

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8113646 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 9]
def baseStart_8113646 : Nat := 118140960795 + 8113646 * 2 ^ 59
def prefixEnd_8113646 : Nat := 4983230072969 + 3 ^ 40 * 8113646 * 2
def baseEnd_8113646 : Nat := 462911139825518617379003

theorem tailTrace_8113646 : CollatzResearch.WordTrace tailWord_8113646 prefixEnd_8113646 462911139825518617379003 := by
  unfold tailWord_8113646
  simp only [CollatzResearch.WordTrace]
  refine ⟨36991122645456714657583099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197285987442435811507109861 36991122645456714657583099)
  ·
    refine ⟨55486683968185071986374649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36991122645456714657583099 55486683968185071986374649)
    ·
      refine ⟨41615012976138803989780987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55486683968185071986374649 41615012976138803989780987)
      ·
        refine ⟨62422519464208205984671481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41615012976138803989780987 62422519464208205984671481)
        ·
          refine ⟨46816889598156154488503611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62422519464208205984671481 46816889598156154488503611)
          ·
            refine ⟨70225334397234231732755417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46816889598156154488503611 70225334397234231732755417)
            ·
              refine ⟨52669000797925673799566563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70225334397234231732755417 52669000797925673799566563)
              ·
                refine ⟨79003501196888510699349845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52669000797925673799566563 79003501196888510699349845)
                ·
                  refine ⟨462911139825518617379003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79003501196888510699349845 462911139825518617379003)
                  ·
                    rfl

theorem cell23_8113646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_8113646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113646 prefixEnd_8113646 := by exact prefixLift 8113646
  have htrace : WordTrace (prefixWord ++ tailWord_8113646) baseStart_8113646 baseEnd_8113646 := by
    simpa [prefixWord, tailWord_8113646, baseEnd_8113646] using wordTrace_append hprefix tailTrace_8113646
  have hstable : (prefixWord ++ tailWord_8113646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113646).length < 2 ^ (prefixWord ++ tailWord_8113646).sum := by decide
  have hdescent : baseEnd_8113646 < baseStart_8113646 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113683 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 2, 5, 2]
def baseStart_8113683 : Nat := 118140960795 + 8113683 * 2 ^ 59
def prefixEnd_8113683 : Nat := 4983230072969 + 3 ^ 40 * 8113683 * 2
def baseEnd_8113683 : Nat := 4166219257213883911648357

theorem tailTrace_8113683 : CollatzResearch.WordTrace tailWord_8113683 prefixEnd_8113683 4166219257213883911648357 := by
  unfold tailWord_8113683
  simp only [CollatzResearch.WordTrace]
  refine ⟨295930330664519672579761703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197286887109679781719841135 295930330664519672579761703)
  ·
    refine ⟨443895495996779508869642555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295930330664519672579761703 443895495996779508869642555)
    ·
      refine ⟨665843243995169263304463833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443895495996779508869642555 665843243995169263304463833)
      ·
        refine ⟨499382432996376947478347875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 665843243995169263304463833 499382432996376947478347875)
        ·
          refine ⟨749073649494565421217521813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499382432996376947478347875 749073649494565421217521813)
          ·
            refine ⟨35112827320057754119571335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 749073649494565421217521813 35112827320057754119571335)
            ·
              refine ⟨52669240980086631179357003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35112827320057754119571335 52669240980086631179357003)
              ·
                refine ⟨79003861470129946769035505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52669240980086631179357003 79003861470129946769035505)
                ·
                  refine ⟨59252896102597460076776629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79003861470129946769035505 59252896102597460076776629)
                  ·
                    refine ⟨5554959009618511882197809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59252896102597460076776629 5554959009618511882197809)
                    ·
                      refine ⟨4166219257213883911648357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5554959009618511882197809 4166219257213883911648357)
                      ·
                        rfl

theorem cell23_8113683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 5, 2].length) (baseStart_8113683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113683 prefixEnd_8113683 := by exact prefixLift 8113683
  have htrace : WordTrace (prefixWord ++ tailWord_8113683) baseStart_8113683 baseEnd_8113683 := by
    simpa [prefixWord, tailWord_8113683, baseEnd_8113683] using wordTrace_append hprefix tailTrace_8113683
  have hstable : (prefixWord ++ tailWord_8113683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113683).length < 2 ^ (prefixWord ++ tailWord_8113683).sum := by decide
  have hdescent : baseEnd_8113683 < baseStart_8113683 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113710 : List Nat := [4, 1, 3, 1, 2, 1, 3, 1, 2, 5]
def baseStart_8113710 : Nat := 118140960795 + 8113710 * 2 ^ 59
def prefixEnd_8113710 : Nat := 4983230072969 + 3 ^ 40 * 8113710 * 2
def baseEnd_8113710 : Nat := 1388744373730518435336911

theorem tailTrace_8113710 : CollatzResearch.WordTrace tailWord_8113710 prefixEnd_8113710 1388744373730518435336911 := by
  unfold tailWord_8113710
  simp only [CollatzResearch.WordTrace]
  refine ⟨36991414429427732023874323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197287543623614570793996389 36991414429427732023874323)
  ·
    refine ⟨55487121644141598035811485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36991414429427732023874323 55487121644141598035811485)
    ·
      refine ⟨20807670616553099263429307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55487121644141598035811485 20807670616553099263429307)
      ·
        refine ⟨31211505924829648895143961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20807670616553099263429307 31211505924829648895143961)
        ·
          refine ⟨23408629443622236671357971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31211505924829648895143961 23408629443622236671357971)
          ·
            refine ⟨35112944165433355007036957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23408629443622236671357971 35112944165433355007036957)
            ·
              refine ⟨13167354062037508127638859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35112944165433355007036957 13167354062037508127638859)
              ·
                refine ⟨19751031093056262191458289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13167354062037508127638859 19751031093056262191458289)
                ·
                  refine ⟨14813273319792196643593717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19751031093056262191458289 14813273319792196643593717)
                  ·
                    refine ⟨1388744373730518435336911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14813273319792196643593717 1388744373730518435336911)
                    ·
                      rfl

theorem cell23_8113710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_8113710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113710 prefixEnd_8113710 := by exact prefixLift 8113710
  have htrace : WordTrace (prefixWord ++ tailWord_8113710) baseStart_8113710 baseEnd_8113710 := by
    simpa [prefixWord, tailWord_8113710, baseEnd_8113710] using wordTrace_append hprefix tailTrace_8113710
  have hstable : (prefixWord ++ tailWord_8113710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113710).length < 2 ^ (prefixWord ++ tailWord_8113710).sum := by decide
  have hdescent : baseEnd_8113710 < baseStart_8113710 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113713 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 3, 6, 2]
def baseStart_8113713 : Nat := 118140960795 + 8113713 * 2 ^ 59
def prefixEnd_8113713 : Nat := 4983230072969 + 3 ^ 40 * 8113713 * 2
def baseEnd_8113713 : Nat := 4166234661633518794273219

theorem tailTrace_8113713 : CollatzResearch.WordTrace tailWord_8113713 prefixEnd_8113713 4166234661633518794273219 := by
  unfold tailWord_8113713
  simp only [CollatzResearch.WordTrace]
  refine ⟨295931424854410987703353793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197287616569607325135569195 295931424854410987703353793)
  ·
    refine ⟨221948568640808240777515345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295931424854410987703353793 221948568640808240777515345)
    ·
      refine ⟨166461426480606180583136509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221948568640808240777515345 166461426480606180583136509)
      ·
        refine ⟨62423034930227317718676191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166461426480606180583136509 62423034930227317718676191)
        ·
          refine ⟨93634552395340976578014287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62423034930227317718676191 93634552395340976578014287)
          ·
            refine ⟨140451828593011464867021431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93634552395340976578014287 140451828593011464867021431)
            ·
              refine ⟨210677742889517197300532147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140451828593011464867021431 210677742889517197300532147)
              ·
                refine ⟨316016614334275795950798221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210677742889517197300532147 316016614334275795950798221)
                ·
                  refine ⟨118506230375353423481549333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316016614334275795950798221 118506230375353423481549333)
                  ·
                    refine ⟨5554979548844691725697625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118506230375353423481549333 5554979548844691725697625)
                    ·
                      refine ⟨4166234661633518794273219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5554979548844691725697625 4166234661633518794273219)
                      ·
                        rfl

theorem cell23_8113713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_8113713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113713 prefixEnd_8113713 := by exact prefixLift 8113713
  have htrace : WordTrace (prefixWord ++ tailWord_8113713) baseStart_8113713 baseEnd_8113713 := by
    simpa [prefixWord, tailWord_8113713, baseEnd_8113713] using wordTrace_append hprefix tailTrace_8113713
  have hstable : (prefixWord ++ tailWord_8113713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113713).length < 2 ^ (prefixWord ++ tailWord_8113713).sum := by decide
  have hdescent : baseEnd_8113713 < baseStart_8113713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113733 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 4, 2, 3]
def baseStart_8113733 : Nat := 118140960795 + 8113733 * 2 ^ 59
def prefixEnd_8113733 : Nat := 4983230072969 + 3 ^ 40 * 8113733 * 2
def baseEnd_8113733 : Nat := 4166244931246608716023127

theorem tailTrace_8113733 : CollatzResearch.WordTrace tailWord_8113733 prefixEnd_8113733 4166244931246608716023127 := by
  unfold tailWord_8113733
  simp only [CollatzResearch.WordTrace]
  refine ⟨295932154314338531119081853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197288102876225687412721235 295932154314338531119081853)
  ·
    refine ⟨110974557867876949169655695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295932154314338531119081853 110974557867876949169655695)
    ·
      refine ⟨166461836801815423754483543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110974557867876949169655695 166461836801815423754483543)
      ·
        refine ⟨249692755202723135631725315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166461836801815423754483543 249692755202723135631725315)
        ·
          refine ⟨374539132804084703447587973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249692755202723135631725315 374539132804084703447587973)
          ·
            refine ⟨70226087400765881896422745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 374539132804084703447587973 70226087400765881896422745)
            ·
              refine ⟨52669565550574411422317059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70226087400765881896422745 52669565550574411422317059)
              ·
                refine ⟨79004348325861617133475589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52669565550574411422317059 79004348325861617133475589)
                ·
                  refine ⟨14813315311099053212526673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79004348325861617133475589 14813315311099053212526673)
                  ·
                    refine ⟨11109986483324289909395005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14813315311099053212526673 11109986483324289909395005)
                    ·
                      refine ⟨4166244931246608716023127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11109986483324289909395005 4166244931246608716023127)
                      ·
                        rfl

theorem cell23_8113733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_8113733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113733 prefixEnd_8113733 := by exact prefixLift 8113733
  have htrace : WordTrace (prefixWord ++ tailWord_8113733) baseStart_8113733 baseEnd_8113733 := by
    simpa [prefixWord, tailWord_8113733, baseEnd_8113733] using wordTrace_append hprefix tailTrace_8113733
  have hstable : (prefixWord ++ tailWord_8113733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113733).length < 2 ^ (prefixWord ++ tailWord_8113733).sum := by decide
  have hdescent : baseEnd_8113733 < baseStart_8113733 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113740 : List Nat := [2, 2, 1, 3, 1, 4, 2, 1, 3, 4]
def baseStart_8113740 : Nat := 118140960795 + 8113740 * 2 ^ 59
def prefixEnd_8113740 : Nat := 4983230072969 + 3 ^ 40 * 8113740 * 2
def baseEnd_8113740 : Nat := 1388749508537063396211865

theorem tailTrace_8113740 : CollatzResearch.WordTrace tailWord_8113740 prefixEnd_8113740 1388749508537063396211865 := by
  unfold tailWord_8113740
  simp only [CollatzResearch.WordTrace]
  refine ⟨147966204812656585657293337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197288273083542114209724449 147966204812656585657293337)
  ·
    refine ⟨110974653609492439242970003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147966204812656585657293337 110974653609492439242970003)
    ·
      refine ⟨166461980414238658864455005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110974653609492439242970003 166461980414238658864455005)
      ·
        refine ⟨62423242655339497074170627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166461980414238658864455005 62423242655339497074170627)
        ·
          refine ⟨93634863983009245611255941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62423242655339497074170627 93634863983009245611255941)
          ·
            refine ⟨17556536996814233552110489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93634863983009245611255941 17556536996814233552110489)
            ·
              refine ⟨13167402747610675164082867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17556536996814233552110489 13167402747610675164082867)
              ·
                refine ⟨19751104121416012746124301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13167402747610675164082867 19751104121416012746124301)
                ·
                  refine ⟨7406664045531004779796613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19751104121416012746124301 7406664045531004779796613)
                  ·
                    refine ⟨1388749508537063396211865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7406664045531004779796613 1388749508537063396211865)
                    ·
                      rfl

theorem cell23_8113740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_8113740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113740 prefixEnd_8113740 := by exact prefixLift 8113740
  have htrace : WordTrace (prefixWord ++ tailWord_8113740) baseStart_8113740 baseEnd_8113740 := by
    simpa [prefixWord, tailWord_8113740, baseEnd_8113740] using wordTrace_append hprefix tailTrace_8113740
  have hstable : (prefixWord ++ tailWord_8113740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113740).length < 2 ^ (prefixWord ++ tailWord_8113740).sum := by decide
  have hdescent : baseEnd_8113740 < baseStart_8113740 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113803 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 4]
def baseStart_8113803 : Nat := 118140960795 + 8113803 * 2 ^ 59
def prefixEnd_8113803 : Nat := 4983230072969 + 3 ^ 40 * 8113803 * 2
def baseEnd_8113803 : Nat := 4166280874892423442147805

theorem tailTrace_8113803 : CollatzResearch.WordTrace tailWord_8113803 prefixEnd_8113803 4166280874892423442147805 := by
  unfold tailWord_8113803
  simp only [CollatzResearch.WordTrace]
  refine ⟨295934707424084933074130063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197289804949389955382753375 295934707424084933074130063)
  ·
    refine ⟨443902061136127399611195095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295934707424084933074130063 443902061136127399611195095)
    ·
      refine ⟨665853091704191099416792643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443902061136127399611195095 665853091704191099416792643)
      ·
        refine ⟨998779637556286649125188965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665853091704191099416792643 998779637556286649125188965)
        ·
          refine ⟨187271182041803746710972931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 998779637556286649125188965 187271182041803746710972931)
          ·
            refine ⟨280906773062705620066459397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187271182041803746710972931 280906773062705620066459397)
            ·
              refine ⟨52670019949257303762461137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280906773062705620066459397 52670019949257303762461137)
              ·
                refine ⟨39502514961942977821845853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52670019949257303762461137 39502514961942977821845853)
                ·
                  refine ⟨14813443110728616683192195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39502514961942977821845853 14813443110728616683192195)
                  ·
                    refine ⟨22220164666092925024788293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14813443110728616683192195 22220164666092925024788293)
                    ·
                      refine ⟨4166280874892423442147805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22220164666092925024788293 4166280874892423442147805)
                      ·
                        rfl

theorem cell23_8113803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 4].length) (baseStart_8113803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113803 prefixEnd_8113803 := by exact prefixLift 8113803
  have htrace : WordTrace (prefixWord ++ tailWord_8113803) baseStart_8113803 baseEnd_8113803 := by
    simpa [prefixWord, tailWord_8113803, baseEnd_8113803] using wordTrace_append hprefix tailTrace_8113803
  have hstable : (prefixWord ++ tailWord_8113803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113803).length < 2 ^ (prefixWord ++ tailWord_8113803).sum := by decide
  have hdescent : baseEnd_8113803 < baseStart_8113803 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113840 : List Nat := [2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 3]
def baseStart_8113840 : Nat := 118140960795 + 8113840 * 2 ^ 59
def prefixEnd_8113840 : Nat := 4983230072969 + 3 ^ 40 * 8113840 * 2
def baseEnd_8113840 : Nat := 4166299873676639797385135

theorem tailTrace_8113840 : CollatzResearch.WordTrace tailWord_8113840 prefixEnd_8113840 4166299873676639797385135 := by
  unfold tailWord_8113840
  simp only [CollatzResearch.WordTrace]
  refine ⟨147968028462475444196613487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197290704616633925595484649 147968028462475444196613487)
  ·
    refine ⟨221952042693713166294920231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147968028462475444196613487 221952042693713166294920231)
    ·
      refine ⟨332928064040569749442380347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221952042693713166294920231 332928064040569749442380347)
      ·
        refine ⟨499392096060854624163570521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332928064040569749442380347 499392096060854624163570521)
        ·
          refine ⟨374544072045640968122677891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499392096060854624163570521 374544072045640968122677891)
          ·
            refine ⟨561816108068461452184016837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374544072045640968122677891 561816108068461452184016837)
            ·
              refine ⟨105340520262836522284503157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 561816108068461452184016837 105340520262836522284503157)
              ·
                refine ⟨9875673774640923964172171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105340520262836522284503157 9875673774640923964172171)
                ·
                  refine ⟨14813510661961385946258257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9875673774640923964172171 14813510661961385946258257)
                  ·
                    refine ⟨11110132996471039459693693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14813510661961385946258257 11110132996471039459693693)
                    ·
                      refine ⟨4166299873676639797385135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11110132996471039459693693 4166299873676639797385135)
                      ·
                        rfl

theorem cell23_8113840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 3].length) (baseStart_8113840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113840 prefixEnd_8113840 := by exact prefixLift 8113840
  have htrace : WordTrace (prefixWord ++ tailWord_8113840) baseStart_8113840 baseEnd_8113840 := by
    simpa [prefixWord, tailWord_8113840, baseEnd_8113840] using wordTrace_append hprefix tailTrace_8113840
  have hstable : (prefixWord ++ tailWord_8113840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113840).length < 2 ^ (prefixWord ++ tailWord_8113840).sum := by decide
  have hdescent : baseEnd_8113840 < baseStart_8113840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113847 : List Nat := [1, 1, 3, 1, 5, 2, 2, 2, 2, 4]
def baseStart_8113847 : Nat := 118140960795 + 8113847 * 2 ^ 59
def prefixEnd_8113847 : Nat := 4983230072969 + 3 ^ 40 * 8113847 * 2
def baseEnd_8113847 : Nat := 1388767822680407089999201

theorem tailTrace_8113847 : CollatzResearch.WordTrace tailWord_8113847 prefixEnd_8113847 1388767822680407089999201 := by
  unfold tailWord_8113847
  simp only [CollatzResearch.WordTrace]
  refine ⟨295936312235925528588731795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197290874823950352392487863 295936312235925528588731795)
  ·
    refine ⟨443904468353888292883097693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295936312235925528588731795 443904468353888292883097693)
    ·
      refine ⟨166464175632708109831161635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443904468353888292883097693 166464175632708109831161635)
      ·
        refine ⟨249696263449062164746742453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166464175632708109831161635 249696263449062164746742453)
        ·
          refine ⟨23409024698349577945007105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249696263449062164746742453 23409024698349577945007105)
          ·
            refine ⟨17556768523762183458755329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23409024698349577945007105 17556768523762183458755329)
            ·
              refine ⟨13167576392821637594066497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17556768523762183458755329 13167576392821637594066497)
              ·
                refine ⟨9875682294616228195549873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13167576392821637594066497 9875682294616228195549873)
                ·
                  refine ⟨7406761720962171146662405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9875682294616228195549873 7406761720962171146662405)
                  ·
                    refine ⟨1388767822680407089999201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7406761720962171146662405 1388767822680407089999201)
                    ·
                      rfl

theorem cell23_8113847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_8113847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113847 prefixEnd_8113847 := by exact prefixLift 8113847
  have htrace : WordTrace (prefixWord ++ tailWord_8113847) baseStart_8113847 baseEnd_8113847 := by
    simpa [prefixWord, tailWord_8113847, baseEnd_8113847] using wordTrace_append hprefix tailTrace_8113847
  have hstable : (prefixWord ++ tailWord_8113847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113847).length < 2 ^ (prefixWord ++ tailWord_8113847).sum := by decide
  have hdescent : baseEnd_8113847 < baseStart_8113847 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113891 : List Nat := [1, 1, 1, 7, 2, 2, 2, 1, 1, 2, 3]
def baseStart_8113891 : Nat := 118140960795 + 8113891 * 2 ^ 59
def prefixEnd_8113891 : Nat := 4983230072969 + 3 ^ 40 * 8113891 * 2
def baseEnd_8113891 : Nat := 4166326061190019097847401

theorem tailTrace_8113891 : CollatzResearch.WordTrace tailWord_8113891 prefixEnd_8113891 4166326061190019097847401 := by
  unfold tailWord_8113891
  simp only [CollatzResearch.WordTrace]
  refine ⟨295937917047766124103333527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197291944698510749402222351 295937917047766124103333527)
  ·
    refine ⟨443906875571649186155000291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295937917047766124103333527 443906875571649186155000291)
    ·
      refine ⟨665860313357473779232500437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443906875571649186155000291 665860313357473779232500437)
      ·
        refine ⟨15606101094315791700761729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 665860313357473779232500437 15606101094315791700761729)
        ·
          refine ⟨11704575820736843775571297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15606101094315791700761729 11704575820736843775571297)
          ·
            refine ⟨8778431865552632831678473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11704575820736843775571297 8778431865552632831678473)
            ·
              refine ⟨6583823899164474623758855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8778431865552632831678473 6583823899164474623758855)
              ·
                refine ⟨9875735848746711935638283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6583823899164474623758855 9875735848746711935638283)
                ·
                  refine ⟨14813603773120067903457425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9875735848746711935638283 14813603773120067903457425)
                  ·
                    refine ⟨11110202829840050927593069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14813603773120067903457425 11110202829840050927593069)
                    ·
                      refine ⟨4166326061190019097847401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11110202829840050927593069 4166326061190019097847401)
                      ·
                        rfl

theorem cell23_8113891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_8113891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113891 prefixEnd_8113891 := by exact prefixLift 8113891
  have htrace : WordTrace (prefixWord ++ tailWord_8113891) baseStart_8113891 baseEnd_8113891 := by
    simpa [prefixWord, tailWord_8113891, baseEnd_8113891] using wordTrace_append hprefix tailTrace_8113891
  have hstable : (prefixWord ++ tailWord_8113891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113891).length < 2 ^ (prefixWord ++ tailWord_8113891).sum := by decide
  have hdescent : baseEnd_8113891 < baseStart_8113891 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113903 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 4, 6]
def baseStart_8113903 : Nat := 118140960795 + 8113903 * 2 ^ 59
def prefixEnd_8113903 : Nat := 4983230072969 + 3 ^ 40 * 8113903 * 2
def baseEnd_8113903 : Nat := 1388777407652624350299115

theorem tailTrace_8113903 : CollatzResearch.WordTrace tailWord_8113903 prefixEnd_8113903 1388777407652624350299115 := by
  unfold tailWord_8113903
  simp only [CollatzResearch.WordTrace]
  refine ⟨295938354723722650152770363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197292236482481766768513575 295938354723722650152770363)
  ·
    refine ⟨443907532085583975229155545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295938354723722650152770363 443907532085583975229155545)
    ·
      refine ⟨332930649064187981421866659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443907532085583975229155545 332930649064187981421866659)
      ·
        refine ⟨499395973596281972132799989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332930649064187981421866659 499395973596281972132799989)
        ·
          refine ⟨46818372524651434887449999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 499395973596281972132799989 46818372524651434887449999)
          ·
            refine ⟨70227558786977152331174999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46818372524651434887449999 70227558786977152331174999)
            ·
              refine ⟨105341338180465728496762499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70227558786977152331174999 105341338180465728496762499)
              ·
                refine ⟨158012007270698592745143749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105341338180465728496762499 158012007270698592745143749)
                ·
                  refine ⟨29627251363255986139714453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158012007270698592745143749 29627251363255986139714453)
                  ·
                    refine ⟨1388777407652624350299115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29627251363255986139714453 1388777407652624350299115)
                    ·
                      rfl

theorem cell23_8113903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 6].length) (baseStart_8113903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113903 prefixEnd_8113903 := by exact prefixLift 8113903
  have htrace : WordTrace (prefixWord ++ tailWord_8113903) baseStart_8113903 baseEnd_8113903 := by
    simpa [prefixWord, tailWord_8113903, baseEnd_8113903] using wordTrace_append hprefix tailTrace_8113903
  have hstable : (prefixWord ++ tailWord_8113903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113903).length < 2 ^ (prefixWord ++ tailWord_8113903).sum := by decide
  have hdescent : baseEnd_8113903 < baseStart_8113903 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113913 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 6, 1, 5]
def baseStart_8113913 : Nat := 118140960795 + 8113913 * 2 ^ 59
def prefixEnd_8113913 : Nat := 4983230072969 + 3 ^ 40 * 8113913 * 2
def baseEnd_8113913 : Nat := 4166337357764418011772299

theorem tailTrace_8113913 : CollatzResearch.WordTrace tailWord_8113913 prefixEnd_8113913 4166337357764418011772299 := by
  unfold tailWord_8113913
  simp only [CollatzResearch.WordTrace]
  refine ⟨295938719453686421860634393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197292479635790947907089595 295938719453686421860634393)
  ·
    refine ⟨221954039590264816395475795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295938719453686421860634393 221954039590264816395475795)
    ·
      refine ⟨332931059385397224593213693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221954039590264816395475795 332931059385397224593213693)
      ·
        refine ⟨124849147269523959222455135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332931059385397224593213693 124849147269523959222455135)
        ·
          refine ⟨187273720904285938833682703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124849147269523959222455135 187273720904285938833682703)
          ·
            refine ⟨280910581356428908250524055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187273720904285938833682703 280910581356428908250524055)
            ·
              refine ⟨421365872034643362375786083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280910581356428908250524055 421365872034643362375786083)
              ·
                refine ⟨632048808051965043563679125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421365872034643362375786083 632048808051965043563679125)
                ·
                  refine ⟨29627287877435861417047459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 632048808051965043563679125 29627287877435861417047459)
                  ·
                    refine ⟨44440931816153792125571189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29627287877435861417047459 44440931816153792125571189)
                    ·
                      refine ⟨4166337357764418011772299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44440931816153792125571189 4166337357764418011772299)
                      ·
                        rfl

theorem cell23_8113913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_8113913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113913 prefixEnd_8113913 := by exact prefixLift 8113913
  have htrace : WordTrace (prefixWord ++ tailWord_8113913) baseStart_8113913 baseEnd_8113913 := by
    simpa [prefixWord, tailWord_8113913, baseEnd_8113913] using wordTrace_append hprefix tailTrace_8113913
  have hstable : (prefixWord ++ tailWord_8113913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113913).length < 2 ^ (prefixWord ++ tailWord_8113913).sum := by decide
  have hdescent : baseEnd_8113913 < baseStart_8113913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113978 : List Nat := [3, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2]
def baseStart_8113978 : Nat := 118140960795 + 8113978 * 2 ^ 59
def prefixEnd_8113978 : Nat := 4983230072969 + 3 ^ 40 * 8113978 * 2
def baseEnd_8113978 : Nat := 4166370734006960257459501

theorem tailTrace_8113978 : CollatzResearch.WordTrace tailWord_8113978 prefixEnd_8113978 4166370734006960257459501 := by
  unfold tailWord_8113978
  simp only [CollatzResearch.WordTrace]
  refine ⟨73985272549612734490437647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197294060132300625307833725 73985272549612734490437647)
  ·
    refine ⟨110977908824419101735656471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73985272549612734490437647 110977908824419101735656471)
    ·
      refine ⟨166466863236628652603484707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110977908824419101735656471 166466863236628652603484707)
      ·
        refine ⟨249700294854942978905227061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166466863236628652603484707 249700294854942978905227061)
        ·
          refine ⟨23409402642650904272365037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249700294854942978905227061 23409402642650904272365037)
          ·
            refine ⟨8778525990994089102136889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23409402642650904272365037 8778525990994089102136889)
            ·
              refine ⟨6583894493245566826602667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8778525990994089102136889 6583894493245566826602667)
              ·
                refine ⟨9875841739868350239904001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6583894493245566826602667 9875841739868350239904001)
                ·
                  refine ⟨7406881304901262679928001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9875841739868350239904001 7406881304901262679928001)
                  ·
                    refine ⟨5555160978675947009946001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7406881304901262679928001 5555160978675947009946001)
                    ·
                      refine ⟨4166370734006960257459501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5555160978675947009946001 4166370734006960257459501)
                      ·
                        rfl

theorem cell23_8113978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2].length) (baseStart_8113978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113978 prefixEnd_8113978 := by exact prefixLift 8113978
  have htrace : WordTrace (prefixWord ++ tailWord_8113978) baseStart_8113978 baseEnd_8113978 := by
    simpa [prefixWord, tailWord_8113978, baseEnd_8113978] using wordTrace_append hprefix tailTrace_8113978
  have hstable : (prefixWord ++ tailWord_8113978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113978).length < 2 ^ (prefixWord ++ tailWord_8113978).sum := by decide
  have hdescent : baseEnd_8113978 < baseStart_8113978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114003 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 9]
def baseStart_8114003 : Nat := 118140960795 + 8114003 * 2 ^ 59
def prefixEnd_8114003 : Nat := 4983230072969 + 3 ^ 40 * 8114003 * 2
def baseEnd_8114003 : Nat := 4166383571023322659646885

theorem tailTrace_8114003 : CollatzResearch.WordTrace tailWord_8114003 prefixEnd_8114003 4166383571023322659646885 := by
  unfold tailWord_8114003
  simp only [CollatzResearch.WordTrace]
  refine ⟨295942002023360367231410663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197294668015573578154273775 295942002023360367231410663)
  ·
    refine ⟨443913003035040550847115995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295942002023360367231410663 443913003035040550847115995)
    ·
      refine ⟨665869504552560826270673993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443913003035040550847115995 665869504552560826270673993)
      ·
        refine ⟨499402128414420619703005495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 665869504552560826270673993 499402128414420619703005495)
        ·
          refine ⟨749103192621630929554508243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499402128414420619703005495 749103192621630929554508243)
          ·
            refine ⟨1123654788932446394331762365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749103192621630929554508243 1123654788932446394331762365)
            ·
              refine ⟨421370545849667397874410887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1123654788932446394331762365 421370545849667397874410887)
              ·
                refine ⟨632055818774501096811616331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421370545849667397874410887 632055818774501096811616331)
                ·
                  refine ⟨948083728161751645217424497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632055818774501096811616331 948083728161751645217424497)
                  ·
                    refine ⟨711062796121313733913068373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 948083728161751645217424497 711062796121313733913068373)
                    ·
                      refine ⟨4166383571023322659646885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 711062796121313733913068373 4166383571023322659646885)
                      ·
                        rfl

theorem cell23_8114003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_8114003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114003 prefixEnd_8114003 := by exact prefixLift 8114003
  have htrace : WordTrace (prefixWord ++ tailWord_8114003) baseStart_8114003 baseEnd_8114003 := by
    simpa [prefixWord, tailWord_8114003, baseEnd_8114003] using wordTrace_append hprefix tailTrace_8114003
  have hstable : (prefixWord ++ tailWord_8114003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114003).length < 2 ^ (prefixWord ++ tailWord_8114003).sum := by decide
  have hdescent : baseEnd_8114003 < baseStart_8114003 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114017 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 2, 4, 2]
def baseStart_8114017 : Nat := 118140960795 + 8114017 * 2 ^ 59
def prefixEnd_8114017 : Nat := 4983230072969 + 3 ^ 40 * 8114017 * 2
def baseEnd_8114017 : Nat := 4166390759752485604871821

theorem tailTrace_8114017 : CollatzResearch.WordTrace tailWord_8114017 prefixEnd_8114017 4166390759752485604871821 := by
  unfold tailWord_8114017
  simp only [CollatzResearch.WordTrace]
  refine ⟨295942512645309647622420305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197295008430206431748280203 295942512645309647622420305)
  ·
    refine ⟨221956884483982235716815229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295942512645309647622420305 221956884483982235716815229)
    ·
      refine ⟨83233831681493338393805711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221956884483982235716815229 83233831681493338393805711)
      ·
        refine ⟨124850747522240007590708567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83233831681493338393805711 124850747522240007590708567)
        ·
          refine ⟨187276121283360011386062851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124850747522240007590708567 187276121283360011386062851)
          ·
            refine ⟨280914181925040017079094277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187276121283360011386062851 280914181925040017079094277)
            ·
              refine ⟨52671409110945003202330177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280914181925040017079094277 52671409110945003202330177)
              ·
                refine ⟨39503556833208752401747633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52671409110945003202330177 39503556833208752401747633)
                ·
                  refine ⟨29627667624906564301310725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39503556833208752401747633 29627667624906564301310725)
                  ·
                    refine ⟨5555187679669980806495761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29627667624906564301310725 5555187679669980806495761)
                    ·
                      refine ⟨4166390759752485604871821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5555187679669980806495761 4166390759752485604871821)
                      ·
                        rfl

theorem cell23_8114017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_8114017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114017 prefixEnd_8114017 := by exact prefixLift 8114017
  have htrace : WordTrace (prefixWord ++ tailWord_8114017) baseStart_8114017 baseEnd_8114017 := by
    simpa [prefixWord, tailWord_8114017, baseEnd_8114017] using wordTrace_append hprefix tailTrace_8114017
  have hstable : (prefixWord ++ tailWord_8114017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114017).length < 2 ^ (prefixWord ++ tailWord_8114017).sum := by decide
  have hdescent : baseEnd_8114017 < baseStart_8114017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114037 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_8114037 : Nat := 118140960795 + 8114037 * 2 ^ 59
def prefixEnd_8114037 : Nat := 4983230072969 + 3 ^ 40 * 8114037 * 2
def baseEnd_8114037 : Nat := 4166401029365575526621729

theorem tailTrace_8114037 : CollatzResearch.WordTrace tailWord_8114037 prefixEnd_8114037 4166401029365575526621729 := by
  unfold tailWord_8114037
  simp only [CollatzResearch.WordTrace]
  refine ⟨295943242105237191038148365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197295494736824794025432243 295943242105237191038148365)
  ·
    refine ⟨110978715789463946639305637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295943242105237191038148365 110978715789463946639305637)
    ·
      refine ⟨20808509210524489994869807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110978715789463946639305637 20808509210524489994869807)
      ·
        refine ⟨31212763815786734992304711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20808509210524489994869807 31212763815786734992304711)
        ·
          refine ⟨46819145723680102488457067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31212763815786734992304711 46819145723680102488457067)
          ·
            refine ⟨70228718585520153732685601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46819145723680102488457067 70228718585520153732685601)
            ·
              refine ⟨52671538939140115299514201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70228718585520153732685601 52671538939140115299514201)
              ·
                refine ⟨39503654204355086474635651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52671538939140115299514201 39503654204355086474635651)
                ·
                  refine ⟨59255481306532629711953477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39503654204355086474635651 59255481306532629711953477)
                  ·
                    refine ⟨11110402744974868070991277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59255481306532629711953477 11110402744974868070991277)
                    ·
                      refine ⟨4166401029365575526621729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11110402744974868070991277 4166401029365575526621729)
                      ·
                        rfl

theorem cell23_8114037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_8114037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114037 prefixEnd_8114037 := by exact prefixLift 8114037
  have htrace : WordTrace (prefixWord ++ tailWord_8114037) baseStart_8114037 baseEnd_8114037 := by
    simpa [prefixWord, tailWord_8114037, baseEnd_8114037] using wordTrace_append hprefix tailTrace_8114037
  have hstable : (prefixWord ++ tailWord_8114037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114037).length < 2 ^ (prefixWord ++ tailWord_8114037).sum := by decide
  have hdescent : baseEnd_8114037 < baseStart_8114037 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114074 : List Nat := [3, 1, 1, 4, 2, 3, 1, 2, 6]
def baseStart_8114074 : Nat := 118140960795 + 8114074 * 2 ^ 59
def prefixEnd_8114074 : Nat := 4983230072969 + 3 ^ 40 * 8114074 * 2
def baseEnd_8114074 : Nat := 462935558683310209095451

theorem tailTrace_8114074 : CollatzResearch.WordTrace tailWord_8114074 prefixEnd_8114074 462935558683310209095451 := by
  unfold tailWord_8114074
  simp only [CollatzResearch.WordTrace]
  refine ⟨73986147901525786589311319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197296394404068764238163517 73986147901525786589311319)
  ·
    refine ⟨110979221852288679883966979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73986147901525786589311319 110979221852288679883966979)
    ·
      refine ⟨166468832778433019825950469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110979221852288679883966979 166468832778433019825950469)
      ·
        refine ⟨31212906145956191217365713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166468832778433019825950469 31212906145956191217365713)
        ·
          refine ⟨23409679609467143413024285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31212906145956191217365713 23409679609467143413024285)
          ·
            refine ⟨8778629853550178779884107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23409679609467143413024285 8778629853550178779884107)
            ·
              refine ⟨13167944780325268169826161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8778629853550178779884107 13167944780325268169826161)
              ·
                refine ⟨9875958585243951127369621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13167944780325268169826161 9875958585243951127369621)
                ·
                  refine ⟨462935558683310209095451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9875958585243951127369621 462935558683310209095451)
                  ·
                    rfl

theorem cell23_8114074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 6].length) (baseStart_8114074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114074 prefixEnd_8114074 := by exact prefixLift 8114074
  have htrace : WordTrace (prefixWord ++ tailWord_8114074) baseStart_8114074 baseEnd_8114074 := by
    simpa [prefixWord, tailWord_8114074, baseEnd_8114074] using wordTrace_append hprefix tailTrace_8114074
  have hstable : (prefixWord ++ tailWord_8114074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114074).length < 2 ^ (prefixWord ++ tailWord_8114074).sum := by decide
  have hdescent : baseEnd_8114074 < baseStart_8114074 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114078 : List Nat := [4, 3, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_8114078 : Nat := 118140960795 + 8114078 * 2 ^ 59
def prefixEnd_8114078 : Nat := 4983230072969 + 3 ^ 40 * 8114078 * 2
def baseEnd_8114078 : Nat := 1388807360690803288736347

theorem tailTrace_8114078 : CollatzResearch.WordTrace tailWord_8114078 prefixEnd_8114078 1388807360690803288736347 := by
  unfold tailWord_8114078
  simp only [CollatzResearch.WordTrace]
  refine ⟨36993092187261081880048861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197296491665392436693593925 36993092187261081880048861)
  ·
    refine ⟨13872409570222905705018323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36993092187261081880048861 13872409570222905705018323)
    ·
      refine ⟨20808614355334358557527485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13872409570222905705018323 20808614355334358557527485)
      ·
        refine ⟨7803230383250384459072807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20808614355334358557527485 7803230383250384459072807)
        ·
          refine ⟨11704845574875576688609211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7803230383250384459072807 11704845574875576688609211)
          ·
            refine ⟨17557268362313365032913817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11704845574875576688609211 17557268362313365032913817)
            ·
              refine ⟨13167951271735023774685363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17557268362313365032913817 13167951271735023774685363)
              ·
                refine ⟨19751926907602535662028045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13167951271735023774685363 19751926907602535662028045)
                ·
                  refine ⟨7406972590350950873260517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19751926907602535662028045 7406972590350950873260517)
                  ·
                    refine ⟨1388807360690803288736347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7406972590350950873260517 1388807360690803288736347)
                    ·
                      rfl

theorem cell23_8114078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_8114078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114078 prefixEnd_8114078 := by exact prefixLift 8114078
  have htrace : WordTrace (prefixWord ++ tailWord_8114078) baseStart_8114078 baseEnd_8114078 := by
    simpa [prefixWord, tailWord_8114078, baseEnd_8114078] using wordTrace_append hprefix tailTrace_8114078
  have hstable : (prefixWord ++ tailWord_8114078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114078).length < 2 ^ (prefixWord ++ tailWord_8114078).sum := by decide
  have hdescent : baseEnd_8114078 < baseStart_8114078 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114084 : List Nat := [2, 3, 1, 2, 1, 3, 1, 3, 3, 1, 3]
def baseStart_8114084 : Nat := 118140960795 + 8114084 * 2 ^ 59
def prefixEnd_8114084 : Nat := 4983230072969 + 3 ^ 40 * 8114084 * 2
def baseEnd_8114084 : Nat := 4166425162956336842734013

theorem tailTrace_8114084 : CollatzResearch.WordTrace tailWord_8114084 prefixEnd_8114084 4166425162956336842734013 := by
  unfold tailWord_8114084
  simp only [CollatzResearch.WordTrace]
  refine ⟨147972478168033459032554653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197296637557377945376739537 147972478168033459032554653)
  ·
    refine ⟨55489679313012547137207995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147972478168033459032554653 55489679313012547137207995)
    ·
      refine ⟨83234518969518820705811993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55489679313012547137207995 83234518969518820705811993)
      ·
        refine ⟨62425889227139115529358995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83234518969518820705811993 62425889227139115529358995)
        ·
          refine ⟨93638833840708673294038493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62425889227139115529358995 93638833840708673294038493)
          ·
            refine ⟨35114562690265752485264435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93638833840708673294038493 35114562690265752485264435)
            ·
              refine ⟨52671844035398628727896653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35114562690265752485264435 52671844035398628727896653)
              ·
                refine ⟨19751941513274485772961245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52671844035398628727896653 19751941513274485772961245)
                ·
                  refine ⟨7406978067477932164860467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19751941513274485772961245 7406978067477932164860467)
                  ·
                    refine ⟨11110467101216898247290701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7406978067477932164860467 11110467101216898247290701)
                    ·
                      refine ⟨4166425162956336842734013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11110467101216898247290701 4166425162956336842734013)
                      ·
                        rfl

theorem cell23_8114084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_8114084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114084 prefixEnd_8114084 := by exact prefixLift 8114084
  have htrace : WordTrace (prefixWord ++ tailWord_8114084) baseStart_8114084 baseEnd_8114084 := by
    simpa [prefixWord, tailWord_8114084, baseEnd_8114084] using wordTrace_append hprefix tailTrace_8114084
  have hstable : (prefixWord ++ tailWord_8114084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114084).length < 2 ^ (prefixWord ++ tailWord_8114084).sum := by decide
  have hdescent : baseEnd_8114084 < baseStart_8114084 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114107 : List Nat := [1, 1, 1, 1, 1, 2, 2, 8, 1, 1, 4]
def baseStart_8114107 : Nat := 118140960795 + 8114107 * 2 ^ 59
def prefixEnd_8114107 : Nat := 4983230072969 + 3 ^ 40 * 8114107 * 2
def baseEnd_8114107 : Nat := 4166436973011390252746407

theorem tailTrace_8114107 : CollatzResearch.WordTrace tailWord_8114107 prefixEnd_8114107 4166436973011390252746407 := by
  unfold tailWord_8114107
  simp only [CollatzResearch.WordTrace]
  refine ⟨295945795214983592993196575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197297196809989061995464383 295945795214983592993196575)
  ·
    refine ⟨443918692822475389489794863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295945795214983592993196575 443918692822475389489794863)
    ·
      refine ⟨665878039233713084234692295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443918692822475389489794863 665878039233713084234692295)
      ·
        refine ⟨998817058850569626352038443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665878039233713084234692295 998817058850569626352038443)
        ·
          refine ⟨1498225588275854439528057665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998817058850569626352038443 1498225588275854439528057665)
          ·
            refine ⟨1123669191206890829646043249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1498225588275854439528057665 1123669191206890829646043249)
            ·
              refine ⟨842751893405168122234532437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123669191206890829646043249 842751893405168122234532437)
              ·
                refine ⟨9875998750841813932435927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 842751893405168122234532437 9875998750841813932435927)
                ·
                  refine ⟨14813998126262720898653891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9875998750841813932435927 14813998126262720898653891)
                  ·
                    refine ⟨22220997189394081347980837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14813998126262720898653891 22220997189394081347980837)
                    ·
                      refine ⟨4166436973011390252746407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22220997189394081347980837 4166436973011390252746407)
                      ·
                        rfl

theorem cell23_8114107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 1, 4].length) (baseStart_8114107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114107 prefixEnd_8114107 := by exact prefixLift 8114107
  have htrace : WordTrace (prefixWord ++ tailWord_8114107) baseStart_8114107 baseEnd_8114107 := by
    simpa [prefixWord, tailWord_8114107, baseEnd_8114107] using wordTrace_append hprefix tailTrace_8114107
  have hstable : (prefixWord ++ tailWord_8114107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114107).length < 2 ^ (prefixWord ++ tailWord_8114107).sum := by decide
  have hdescent : baseEnd_8114107 < baseStart_8114107 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114124 : List Nat := [2, 2, 1, 4, 1, 2, 2, 3, 1, 1, 4]
def baseStart_8114124 : Nat := 118140960795 + 8114124 * 2 ^ 59
def prefixEnd_8114124 : Nat := 4983230072969 + 3 ^ 40 * 8114124 * 2
def baseEnd_8114124 : Nat := 4166445702182516686233829

theorem tailTrace_8114124 : CollatzResearch.WordTrace tailWord_8114124 prefixEnd_8114124 4166445702182516686233829 := by
  unfold tailWord_8114124
  simp only [CollatzResearch.WordTrace]
  refine ⟨147973207627961002448282713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197297610170614669931043617 147973207627961002448282713)
  ·
    refine ⟨110979905720970751836212035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147973207627961002448282713 110979905720970751836212035)
    ·
      refine ⟨166469858581456127754318053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110979905720970751836212035 166469858581456127754318053)
      ·
        refine ⟨31213098484023023953934635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166469858581456127754318053 31213098484023023953934635)
        ·
          refine ⟨46819647726034535930901953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31213098484023023953934635 46819647726034535930901953)
          ·
            refine ⟨35114735794525901948176465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46819647726034535930901953 35114735794525901948176465)
            ·
              refine ⟨26336051845894426461132349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35114735794525901948176465 26336051845894426461132349)
              ·
                refine ⟨9876019442210409922924631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26336051845894426461132349 9876019442210409922924631)
                ·
                  refine ⟨14814029163315614884386947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9876019442210409922924631 14814029163315614884386947)
                  ·
                    refine ⟨22221043744973422326580421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14814029163315614884386947 22221043744973422326580421)
                    ·
                      refine ⟨4166445702182516686233829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22221043744973422326580421 4166445702182516686233829)
                      ·
                        rfl

theorem cell23_8114124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_8114124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114124 prefixEnd_8114124 := by exact prefixLift 8114124
  have htrace : WordTrace (prefixWord ++ tailWord_8114124) baseStart_8114124 baseEnd_8114124 := by
    simpa [prefixWord, tailWord_8114124, baseEnd_8114124] using wordTrace_append hprefix tailTrace_8114124
  have hstable : (prefixWord ++ tailWord_8114124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114124).length < 2 ^ (prefixWord ++ tailWord_8114124).sum := by decide
  have hdescent : baseEnd_8114124 < baseStart_8114124 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114127 : List Nat := [1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 5]
def baseStart_8114127 : Nat := 118140960795 + 8114127 * 2 ^ 59
def prefixEnd_8114127 : Nat := 4983230072969 + 3 ^ 40 * 8114127 * 2
def baseEnd_8114127 : Nat := 4166447242624480174496315

theorem tailTrace_8114127 : CollatzResearch.WordTrace tailWord_8114127 prefixEnd_8114127 4166447242624480174496315 := by
  unfold tailWord_8114127
  simp only [CollatzResearch.WordTrace]
  refine ⟨295946524674911136408924635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197297683116607424272616423 295946524674911136408924635)
  ·
    refine ⟨443919787012366704613386953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295946524674911136408924635 443919787012366704613386953)
    ·
      refine ⟨332939840259275028460040215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443919787012366704613386953 332939840259275028460040215)
      ·
        refine ⟨499409760388912542690060323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332939840259275028460040215 499409760388912542690060323)
        ·
          refine ⟨749114640583368814035090485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499409760388912542690060323 749114640583368814035090485)
          ·
            refine ⟨70229497554690826315789733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 749114640583368814035090485 70229497554690826315789733)
            ·
              refine ⟨13168030791504529934210575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70229497554690826315789733 13168030791504529934210575)
              ·
                refine ⟨19752046187256794901315863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13168030791504529934210575 19752046187256794901315863)
                ·
                  refine ⟨29628069280885192351973795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19752046187256794901315863 29628069280885192351973795)
                  ·
                    refine ⟨44442103921327788527960693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29628069280885192351973795 44442103921327788527960693)
                    ·
                      refine ⟨4166447242624480174496315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44442103921327788527960693 4166447242624480174496315)
                      ·
                        rfl

theorem cell23_8114127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 5].length) (baseStart_8114127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114127 prefixEnd_8114127 := by exact prefixLift 8114127
  have htrace : WordTrace (prefixWord ++ tailWord_8114127) baseStart_8114127 baseEnd_8114127 := by
    simpa [prefixWord, tailWord_8114127, baseEnd_8114127] using wordTrace_append hprefix tailTrace_8114127
  have hstable : (prefixWord ++ tailWord_8114127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114127).length < 2 ^ (prefixWord ++ tailWord_8114127).sum := by decide
  have hdescent : baseEnd_8114127 < baseStart_8114127 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114147 : List Nat := [1, 1, 1, 6, 1, 3, 2, 8]
def baseStart_8114147 : Nat := 118140960795 + 8114147 * 2 ^ 59
def prefixEnd_8114147 : Nat := 4983230072969 + 3 ^ 40 * 8114147 * 2
def baseEnd_8114147 : Nat := 154313241193984077638749

theorem tailTrace_8114147 : CollatzResearch.WordTrace tailWord_8114147 prefixEnd_8114147 154313241193984077638749 := by
  unfold tailWord_8114147
  simp only [CollatzResearch.WordTrace]
  refine ⟨295947254134838679824652695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197298169423225786549768463 295947254134838679824652695)
  ·
    refine ⟨443920881202258019736979043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295947254134838679824652695 443920881202258019736979043)
    ·
      refine ⟨665881321803387029605468565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443920881202258019736979043 665881321803387029605468565)
      ·
        refine ⟨31213186959533767012756339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 665881321803387029605468565 31213186959533767012756339)
        ·
          refine ⟨46819780439300650519134509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31213186959533767012756339 46819780439300650519134509)
          ·
            refine ⟨17557417664737743944675441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46819780439300650519134509 17557417664737743944675441)
            ·
              refine ⟨13168063248553307958506581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17557417664737743944675441 13168063248553307958506581)
              ·
                refine ⟨154313241193984077638749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13168063248553307958506581 154313241193984077638749)
                ·
                  rfl

theorem cell23_8114147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 8].length) (baseStart_8114147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114147 prefixEnd_8114147 := by exact prefixLift 8114147
  have htrace : WordTrace (prefixWord ++ tailWord_8114147) baseStart_8114147 baseEnd_8114147 := by
    simpa [prefixWord, tailWord_8114147, baseEnd_8114147] using wordTrace_append hprefix tailTrace_8114147
  have hstable : (prefixWord ++ tailWord_8114147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114147).length < 2 ^ (prefixWord ++ tailWord_8114147).sum := by decide
  have hdescent : baseEnd_8114147 < baseStart_8114147 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114151 : List Nat := [1, 1, 5, 2, 3, 1, 1, 3, 2, 4]
def baseStart_8114151 : Nat := 118140960795 + 8114151 * 2 ^ 59
def prefixEnd_8114151 : Nat := 4983230072969 + 3 ^ 40 * 8114151 * 2
def baseEnd_8114151 : Nat := 1388819855386729360198735

theorem tailTrace_8114151 : CollatzResearch.WordTrace tailWord_8114151 prefixEnd_8114151 1388819855386729360198735 := by
  unfold tailWord_8114151
  simp only [CollatzResearch.WordTrace]
  refine ⟨295947400026824188507798307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197298266684549459005198871 295947400026824188507798307)
  ·
    refine ⟨443921100040236282761697461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295947400026824188507798307 443921100040236282761697461)
    ·
      refine ⟨41617603128772151508909137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 443921100040236282761697461 41617603128772151508909137)
      ·
        refine ⟨31213202346579113631681853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41617603128772151508909137 31213202346579113631681853)
        ·
          refine ⟨11704950879967167611880695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31213202346579113631681853 11704950879967167611880695)
          ·
            refine ⟨17557426319950751417821043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11704950879967167611880695 17557426319950751417821043)
            ·
              refine ⟨26336139479926127126731565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17557426319950751417821043 26336139479926127126731565)
              ·
                refine ⟨9876052304972297672524337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26336139479926127126731565 9876052304972297672524337)
                ·
                  refine ⟨7407039228729223254393253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9876052304972297672524337 7407039228729223254393253)
                  ·
                    refine ⟨1388819855386729360198735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7407039228729223254393253 1388819855386729360198735)
                    ·
                      rfl

theorem cell23_8114151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_8114151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114151 prefixEnd_8114151 := by exact prefixLift 8114151
  have htrace : WordTrace (prefixWord ++ tailWord_8114151) baseStart_8114151 baseEnd_8114151 := by
    simpa [prefixWord, tailWord_8114151, baseEnd_8114151] using wordTrace_append hprefix tailTrace_8114151
  have hstable : (prefixWord ++ tailWord_8114151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114151).length < 2 ^ (prefixWord ++ tailWord_8114151).sum := by decide
  have hdescent : baseEnd_8114151 < baseStart_8114151 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114207 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 2, 6]
def baseStart_8114207 : Nat := 118140960795 + 8114207 * 2 ^ 59
def prefixEnd_8114207 : Nat := 4983230072969 + 3 ^ 40 * 8114207 * 2
def baseEnd_8114207 : Nat := 1388829440358946620498649

theorem tailTrace_8114207 : CollatzResearch.WordTrace tailWord_8114207 prefixEnd_8114207 1388829440358946620498649 := by
  unfold tailWord_8114207
  simp only [CollatzResearch.WordTrace]
  refine ⟨295949442514621310071836875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197299628343080873381224583 295949442514621310071836875)
  ·
    refine ⟨443924163771931965107755313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295949442514621310071836875 443924163771931965107755313)
    ·
      refine ⟨332943122828948973830816485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443924163771931965107755313 332943122828948973830816485)
      ·
        refine ⟨62426835530427932593278091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332943122828948973830816485 62426835530427932593278091)
        ·
          refine ⟨93640253295641898889917137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62426835530427932593278091 93640253295641898889917137)
          ·
            refine ⟨70230189971731424167437853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93640253295641898889917137 70230189971731424167437853)
            ·
              refine ⟨26336321239399284062789195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70230189971731424167437853 26336321239399284062789195)
              ·
                refine ⟨39504481859098926094183793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26336321239399284062789195 39504481859098926094183793)
                ·
                  refine ⟨29628361394324194570637845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39504481859098926094183793 29628361394324194570637845)
                  ·
                    refine ⟨1388829440358946620498649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29628361394324194570637845 1388829440358946620498649)
                    ·
                      rfl

theorem cell23_8114207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 6].length) (baseStart_8114207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114207 prefixEnd_8114207 := by exact prefixLift 8114207
  have htrace : WordTrace (prefixWord ++ tailWord_8114207) baseStart_8114207 baseEnd_8114207 := by
    simpa [prefixWord, tailWord_8114207, baseEnd_8114207] using wordTrace_append hprefix tailTrace_8114207
  have hstable : (prefixWord ++ tailWord_8114207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114207).length < 2 ^ (prefixWord ++ tailWord_8114207).sum := by decide
  have hdescent : baseEnd_8114207 < baseStart_8114207 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114237 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 9]
def baseStart_8114237 : Nat := 118140960795 + 8114237 * 2 ^ 59
def prefixEnd_8114237 : Nat := 4983230072969 + 3 ^ 40 * 8114237 * 2
def baseEnd_8114237 : Nat := 462944858388497193791201

theorem tailTrace_8114237 : CollatzResearch.WordTrace tailWord_8114237 prefixEnd_8114237 462944858388497193791201 := by
  unfold tailWord_8114237
  simp only [CollatzResearch.WordTrace]
  refine ⟨295950536704512625195428965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197300357803008416796952643 295950536704512625195428965)
  ·
    refine ⟨55490725632096117224142931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295950536704512625195428965 55490725632096117224142931)
    ·
      refine ⟨83236088448144175836214397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55490725632096117224142931 83236088448144175836214397)
      ·
        refine ⟨31213533168054065938580399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83236088448144175836214397 31213533168054065938580399)
        ·
          refine ⟨46820299752081098907870599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31213533168054065938580399 46820299752081098907870599)
          ·
            refine ⟨70230449628121648361805899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46820299752081098907870599 70230449628121648361805899)
            ·
              refine ⟨105345674442182472542708849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70230449628121648361805899 105345674442182472542708849)
              ·
                refine ⟨79009255831636854407031637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105345674442182472542708849 79009255831636854407031637)
                ·
                  refine ⟨462944858388497193791201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79009255831636854407031637 462944858388497193791201)
                  ·
                    rfl

theorem cell23_8114237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_8114237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114237 prefixEnd_8114237 := by exact prefixLift 8114237
  have htrace : WordTrace (prefixWord ++ tailWord_8114237) baseStart_8114237 baseEnd_8114237 := by
    simpa [prefixWord, tailWord_8114237, baseEnd_8114237] using wordTrace_append hprefix tailTrace_8114237
  have hstable : (prefixWord ++ tailWord_8114237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114237).length < 2 ^ (prefixWord ++ tailWord_8114237).sum := by decide
  have hdescent : baseEnd_8114237 < baseStart_8114237 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114254 : List Nat := [4, 1, 1, 1, 1, 5, 2, 1, 7]
def baseStart_8114254 : Nat := 118140960795 + 8114254 * 2 ^ 59
def prefixEnd_8114254 : Nat := 4983230072969 + 3 ^ 40 * 8114254 * 2
def baseEnd_8114254 : Nat := 462945828296400130845359

theorem tailTrace_8114254 : CollatzResearch.WordTrace tailWord_8114254 prefixEnd_8114254 462945828296400130845359 := by
  unfold tailWord_8114254
  simp only [CollatzResearch.WordTrace]
  refine ⟨36993894593181379637349727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197300771163634024732531877 36993894593181379637349727)
  ·
    refine ⟨55490841889772069456024591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36993894593181379637349727 55490841889772069456024591)
    ·
      refine ⟨83236262834658104184036887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55490841889772069456024591 83236262834658104184036887)
      ·
        refine ⟨124854394251987156276055331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83236262834658104184036887 124854394251987156276055331)
        ·
          refine ⟨187281591377980734414082997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124854394251987156276055331 187281591377980734414082997)
          ·
            refine ⟨17557649191685693851320281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187281591377980734414082997 17557649191685693851320281)
            ·
              refine ⟨13168236893764270388490211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17557649191685693851320281 13168236893764270388490211)
              ·
                refine ⟨19752355340646405582735317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13168236893764270388490211 19752355340646405582735317)
                ·
                  refine ⟨462945828296400130845359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19752355340646405582735317 462945828296400130845359)
                  ·
                    rfl

theorem cell23_8114254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_8114254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114254 prefixEnd_8114254 := by exact prefixLift 8114254
  have htrace : WordTrace (prefixWord ++ tailWord_8114254) baseStart_8114254 baseEnd_8114254 := by
    simpa [prefixWord, tailWord_8114254, baseEnd_8114254] using wordTrace_append hprefix tailTrace_8114254
  have hstable : (prefixWord ++ tailWord_8114254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114254).length < 2 ^ (prefixWord ++ tailWord_8114254).sum := by decide
  have hdescent : baseEnd_8114254 < baseStart_8114254 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114264 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 2, 3, 3]
def baseStart_8114264 : Nat := 118140960795 + 8114264 * 2 ^ 59
def prefixEnd_8114264 : Nat := 4983230072969 + 3 ^ 40 * 8114264 * 2
def baseEnd_8114264 : Nat := 4166517589474146138483185

theorem tailTrace_8114264 : CollatzResearch.WordTrace tailWord_8114264 prefixEnd_8114264 4166517589474146138483185 := by
  unfold tailWord_8114264
  simp only [CollatzResearch.WordTrace]
  refine ⟨147975760737707404403330923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197301014316943205871107897 147975760737707404403330923)
  ·
    refine ⟨221963641106561106604996385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147975760737707404403330923 221963641106561106604996385)
    ·
      refine ⟨166472730829920829953747289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221963641106561106604996385 166472730829920829953747289)
      ·
        refine ⟨124854548122440622465310467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166472730829920829953747289 124854548122440622465310467)
        ·
          refine ⟨187281822183660933697965701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124854548122440622465310467 187281822183660933697965701)
          ·
            refine ⟨35115341659436425068368569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187281822183660933697965701 35115341659436425068368569)
            ·
              refine ⟨26336506244577318801276427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35115341659436425068368569 26336506244577318801276427)
              ·
                refine ⟨39504759366865978201914641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26336506244577318801276427 39504759366865978201914641)
                ·
                  refine ⟨29628569525149483651435981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39504759366865978201914641 29628569525149483651435981)
                  ·
                    refine ⟨11110713571931056369288493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29628569525149483651435981 11110713571931056369288493)
                    ·
                      refine ⟨4166517589474146138483185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11110713571931056369288493 4166517589474146138483185)
                      ·
                        rfl

theorem cell23_8114264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_8114264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114264 prefixEnd_8114264 := by exact prefixLift 8114264
  have htrace : WordTrace (prefixWord ++ tailWord_8114264) baseStart_8114264 baseEnd_8114264 := by
    simpa [prefixWord, tailWord_8114264, baseEnd_8114264] using wordTrace_append hprefix tailTrace_8114264
  have hstable : (prefixWord ++ tailWord_8114264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114264).length < 2 ^ (prefixWord ++ tailWord_8114264).sum := by decide
  have hdescent : baseEnd_8114264 < baseStart_8114264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114338 : List Nat := [3, 3, 1, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_8114338 : Nat := 118140960795 + 8114338 * 2 ^ 59
def prefixEnd_8114338 : Nat := 4983230072969 + 3 ^ 40 * 8114338 * 2
def baseEnd_8114338 : Nat := 4166555587042578848957845

theorem tailTrace_8114338 : CollatzResearch.WordTrace tailWord_8114338 prefixEnd_8114338 4166555587042578848957845 := by
  unfold tailWord_8114338
  simp only [CollatzResearch.WordTrace]
  refine ⟨73988555119286679861213917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197302813651431146296570445 73988555119286679861213917)
  ·
    refine ⟨27745708169732504947955219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73988555119286679861213917 27745708169732504947955219)
    ·
      refine ⟨41618562254598757421932829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27745708169732504947955219 41618562254598757421932829)
      ·
        refine ⟨15606960845474534033224811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41618562254598757421932829 15606960845474534033224811)
        ·
          refine ⟨23410441268211801049837217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15606960845474534033224811 23410441268211801049837217)
          ·
            refine ⟨17557830951158850787377913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23410441268211801049837217 17557830951158850787377913)
            ·
              refine ⟨13168373213369138090533435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17557830951158850787377913 13168373213369138090533435)
              ·
                refine ⟨19752559820053707135800153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13168373213369138090533435 19752559820053707135800153)
                ·
                  refine ⟨14814419865040280351850115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19752559820053707135800153 14814419865040280351850115)
                  ·
                    refine ⟨22221629797560420527775173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14814419865040280351850115 22221629797560420527775173)
                    ·
                      refine ⟨4166555587042578848957845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22221629797560420527775173 4166555587042578848957845)
                      ·
                        rfl

theorem cell23_8114338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_8114338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114338 prefixEnd_8114338 := by exact prefixLift 8114338
  have htrace : WordTrace (prefixWord ++ tailWord_8114338) baseStart_8114338 baseEnd_8114338 := by
    simpa [prefixWord, tailWord_8114338, baseEnd_8114338] using wordTrace_append hprefix tailTrace_8114338
  have hstable : (prefixWord ++ tailWord_8114338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114338).length < 2 ^ (prefixWord ++ tailWord_8114338).sum := by decide
  have hdescent : baseEnd_8114338 < baseStart_8114338 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114341 : List Nat := [1, 3, 1, 2, 1, 3, 4, 1, 2, 2, 3]
def baseStart_8114341 : Nat := 118140960795 + 8114341 * 2 ^ 59
def prefixEnd_8114341 : Nat := 4983230072969 + 3 ^ 40 * 8114341 * 2
def baseEnd_8114341 : Nat := 4166557127484542337220331

theorem tailTrace_8114341 : CollatzResearch.WordTrace tailWord_8114341 prefixEnd_8114341 4166557127484542337220331 := by
  unfold tailWord_8114341
  simp only [CollatzResearch.WordTrace]
  refine ⟨295954329896135850957214877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197302886597423900638143251 295954329896135850957214877)
  ·
    refine ⟨110982873711050944108955579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295954329896135850957214877 110982873711050944108955579)
    ·
      refine ⟨166474310566576416163433369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110982873711050944108955579 166474310566576416163433369)
      ·
        refine ⟨124855732924932312122575027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166474310566576416163433369 124855732924932312122575027)
        ·
          refine ⟨187283599387398468183862541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124855732924932312122575027 187283599387398468183862541)
          ·
            refine ⟨70231349770274425568948453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187283599387398468183862541 70231349770274425568948453)
            ·
              refine ⟨13168378081926454794177835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70231349770274425568948453 13168378081926454794177835)
              ·
                refine ⟨19752567122889682191266753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13168378081926454794177835 19752567122889682191266753)
                ·
                  refine ⟨14814425342167261643450065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19752567122889682191266753 14814425342167261643450065)
                  ·
                    refine ⟨11110819006625446232587549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14814425342167261643450065 11110819006625446232587549)
                    ·
                      refine ⟨4166557127484542337220331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11110819006625446232587549 4166557127484542337220331)
                      ·
                        rfl

theorem cell23_8114341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_8114341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114341 prefixEnd_8114341 := by exact prefixLift 8114341
  have htrace : WordTrace (prefixWord ++ tailWord_8114341) baseStart_8114341 baseEnd_8114341 := by
    simpa [prefixWord, tailWord_8114341, baseEnd_8114341] using wordTrace_append hprefix tailTrace_8114341
  have hstable : (prefixWord ++ tailWord_8114341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114341).length < 2 ^ (prefixWord ++ tailWord_8114341).sum := by decide
  have hdescent : baseEnd_8114341 < baseStart_8114341 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114356 : List Nat := [2, 5, 3, 1, 2, 1, 2, 2, 5]
def baseStart_8114356 : Nat := 118140960795 + 8114356 * 2 ^ 59
def prefixEnd_8114356 : Nat := 4983230072969 + 3 ^ 40 * 8114356 * 2
def baseEnd_8114356 : Nat := 462951647743817753170307

theorem tailTrace_8114356 : CollatzResearch.WordTrace tailWord_8114356 prefixEnd_8114356 462951647743817753170307 := by
  unfold tailWord_8114356
  simp only [CollatzResearch.WordTrace]
  refine ⟨147977438495540754259505461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197303251327387672346007281 147977438495540754259505461)
  ·
    refine ⟨13872884858956945711828637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147977438495540754259505461 13872884858956945711828637)
    ·
      refine ⟨5202331822108854641935739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13872884858956945711828637 5202331822108854641935739)
      ·
        refine ⟨7803497733163281962903609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5202331822108854641935739 7803497733163281962903609)
        ·
          refine ⟨5852623299872461472177707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7803497733163281962903609 5852623299872461472177707)
          ·
            refine ⟨8778934949808692208266561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5852623299872461472177707 8778934949808692208266561)
            ·
              refine ⟨6584201212356519156199921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8778934949808692208266561 6584201212356519156199921)
              ·
                refine ⟨4938150909267389367149941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6584201212356519156199921 4938150909267389367149941)
                ·
                  refine ⟨462951647743817753170307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4938150909267389367149941 462951647743817753170307)
                  ·
                    rfl

theorem cell23_8114356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_8114356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114356 prefixEnd_8114356 := by exact prefixLift 8114356
  have htrace : WordTrace (prefixWord ++ tailWord_8114356) baseStart_8114356 baseEnd_8114356 := by
    simpa [prefixWord, tailWord_8114356, baseEnd_8114356] using wordTrace_append hprefix tailTrace_8114356
  have hstable : (prefixWord ++ tailWord_8114356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114356).length < 2 ^ (prefixWord ++ tailWord_8114356).sum := by decide
  have hdescent : baseEnd_8114356 < baseStart_8114356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114405 : List Nat := [1, 3, 1, 4, 2, 1, 1, 5, 1, 1, 3]
def baseStart_8114405 : Nat := 118140960795 + 8114405 * 2 ^ 59
def prefixEnd_8114405 : Nat := 4983230072969 + 3 ^ 40 * 8114405 * 2
def baseEnd_8114405 : Nat := 4166589990246430086820037

theorem tailTrace_8114405 : CollatzResearch.WordTrace tailWord_8114405 prefixEnd_8114405 4166589990246430086820037 := by
  unfold tailWord_8114405
  simp only [CollatzResearch.WordTrace]
  refine ⟨295956664167903989887544669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197304442778602659925029779 295956664167903989887544669)
  ·
    refine ⟨110983749062963996207829251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295956664167903989887544669 110983749062963996207829251)
    ·
      refine ⟨166475623594445994311743877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110983749062963996207829251 166475623594445994311743877)
      ·
        refine ⟨31214179423958623933451977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166475623594445994311743877 31214179423958623933451977)
        ·
          refine ⟨23410634567968967950088983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31214179423958623933451977 23410634567968967950088983)
          ·
            refine ⟨35115951851953451925133475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23410634567968967950088983 35115951851953451925133475)
            ·
              refine ⟨52673927777930177887700213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35115951851953451925133475 52673927777930177887700213)
              ·
                refine ⟨4938180729180954176971895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52673927777930177887700213 4938180729180954176971895)
                ·
                  refine ⟨7407271093771431265457843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4938180729180954176971895 7407271093771431265457843)
                  ·
                    refine ⟨11110906640657146898186765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7407271093771431265457843 11110906640657146898186765)
                    ·
                      refine ⟨4166589990246430086820037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11110906640657146898186765 4166589990246430086820037)
                      ·
                        rfl

theorem cell23_8114405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_8114405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114405 prefixEnd_8114405 := by exact prefixLift 8114405
  have htrace : WordTrace (prefixWord ++ tailWord_8114405) baseStart_8114405 baseEnd_8114405 := by
    simpa [prefixWord, tailWord_8114405, baseEnd_8114405] using wordTrace_append hprefix tailTrace_8114405
  have hstable : (prefixWord ++ tailWord_8114405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114405).length < 2 ^ (prefixWord ++ tailWord_8114405).sum := by decide
  have hdescent : baseEnd_8114405 < baseStart_8114405 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114408 : List Nat := [2, 1, 4, 1, 2, 2, 4, 1, 1, 5]
def baseStart_8114408 : Nat := 118140960795 + 8114408 * 2 ^ 59
def prefixEnd_8114408 : Nat := 4983230072969 + 3 ^ 40 * 8114408 * 2
def baseEnd_8114408 : Nat := 1388863843562797858360841

theorem tailTrace_8114408 : CollatzResearch.WordTrace tailWord_8114408 prefixEnd_8114408 1388863843562797858360841 := by
  unfold tailWord_8114408
  simp only [CollatzResearch.WordTrace]
  refine ⟨147978386793446560699951939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197304515724595414266602585 147978386793446560699951939)
  ·
    refine ⟨221967580190169841049927909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147978386793446560699951939 221967580190169841049927909)
    ·
      refine ⟨41618921285656845196861483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221967580190169841049927909 41618921285656845196861483)
      ·
        refine ⟨62428381928485267795292225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41618921285656845196861483 62428381928485267795292225)
        ·
          refine ⟨46821286446363950846469169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62428381928485267795292225 46821286446363950846469169)
          ·
            refine ⟨35115964834772963134851877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46821286446363950846469169 35115964834772963134851877)
            ·
              refine ⟨6584243406519930587784727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35115964834772963134851877 6584243406519930587784727)
              ·
                refine ⟨9876365109779895881677091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6584243406519930587784727 9876365109779895881677091)
                ·
                  refine ⟨14814547664669843822515637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9876365109779895881677091 14814547664669843822515637)
                  ·
                    refine ⟨1388863843562797858360841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14814547664669843822515637 1388863843562797858360841)
                    ·
                      rfl

theorem cell23_8114408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_8114408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114408 prefixEnd_8114408 := by exact prefixLift 8114408
  have htrace : WordTrace (prefixWord ++ tailWord_8114408) baseStart_8114408 baseEnd_8114408 := by
    simpa [prefixWord, tailWord_8114408, baseEnd_8114408] using wordTrace_append hprefix tailTrace_8114408
  have hstable : (prefixWord ++ tailWord_8114408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114408).length < 2 ^ (prefixWord ++ tailWord_8114408).sum := by decide
  have hdescent : baseEnd_8114408 < baseStart_8114408 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114411 : List Nat := [1, 1, 1, 1, 2, 5, 3, 3, 1, 1, 4]
def baseStart_8114411 : Nat := 118140960795 + 8114411 * 2 ^ 59
def prefixEnd_8114411 : Nat := 4983230072969 + 3 ^ 40 * 8114411 * 2
def baseEnd_8114411 : Nat := 4166593071130357063345009

theorem tailTrace_8114411 : CollatzResearch.WordTrace tailWord_8114411 prefixEnd_8114411 4166593071130357063345009 := by
  unfold tailWord_8114411
  simp only [CollatzResearch.WordTrace]
  refine ⟨295956883005882252912263087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197304588670588168608175391 295956883005882252912263087)
  ·
    refine ⟨443935324508823379368394631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295956883005882252912263087 443935324508823379368394631)
    ·
      refine ⟨665902986763235069052591947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443935324508823379368394631 665902986763235069052591947)
      ·
        refine ⟨998854480144852603578887921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665902986763235069052591947 998854480144852603578887921)
        ·
          refine ⟨749140860108639452684165941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 998854480144852603578887921 749140860108639452684165941)
          ·
            refine ⟨70231955635184948689140557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 749140860108639452684165941 70231955635184948689140557)
            ·
              refine ⟨26336983363194355758427709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70231955635184948689140557 26336983363194355758427709)
              ·
                refine ⟨9876368761197883409410391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26336983363194355758427709 9876368761197883409410391)
                ·
                  refine ⟨14814553141796825114115587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9876368761197883409410391 14814553141796825114115587)
                  ·
                    refine ⟨22221829712695237671173381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14814553141796825114115587 22221829712695237671173381)
                    ·
                      refine ⟨4166593071130357063345009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22221829712695237671173381 4166593071130357063345009)
                      ·
                        rfl

theorem cell23_8114411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 1, 4].length) (baseStart_8114411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114411 prefixEnd_8114411 := by exact prefixLift 8114411
  have htrace : WordTrace (prefixWord ++ tailWord_8114411) baseStart_8114411 baseEnd_8114411 := by
    simpa [prefixWord, tailWord_8114411, baseEnd_8114411] using wordTrace_append hprefix tailTrace_8114411
  have hstable : (prefixWord ++ tailWord_8114411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114411).length < 2 ^ (prefixWord ++ tailWord_8114411).sum := by decide
  have hdescent : baseEnd_8114411 < baseStart_8114411 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114424 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 3, 2, 4]
def baseStart_8114424 : Nat := 118140960795 + 8114424 * 2 ^ 59
def prefixEnd_8114424 : Nat := 4983230072969 + 3 ^ 40 * 8114424 * 2
def baseEnd_8114424 : Nat := 4166599746378865512482449

theorem tailTrace_8114424 : CollatzResearch.WordTrace tailWord_8114424 prefixEnd_8114424 4166599746378865512482449 := by
  unfold tailWord_8114424
  simp only [CollatzResearch.WordTrace]
  refine ⟨147978678577417578066243163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197304904769890104088324217 147978678577417578066243163)
  ·
    refine ⟨221968017866126367099364745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147978678577417578066243163 221968017866126367099364745)
    ·
      refine ⟨166476013399594775324523559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221968017866126367099364745 166476013399594775324523559)
      ·
        refine ⟨249714020099392162986785339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166476013399594775324523559 249714020099392162986785339)
        ·
          refine ⟨374571030149088244480178009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249714020099392162986785339 374571030149088244480178009)
          ·
            refine ⟨280928272611816183360133507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374571030149088244480178009 280928272611816183360133507)
            ·
              refine ⟨421392408917724275040200261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280928272611816183360133507 421392408917724275040200261)
              ·
                refine ⟨79011076672073301570037549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 421392408917724275040200261 79011076672073301570037549)
                ·
                  refine ⟨29629153752027488088764081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79011076672073301570037549 29629153752027488088764081)
                  ·
                    refine ⟨22221865314020616066573061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29629153752027488088764081 22221865314020616066573061)
                    ·
                      refine ⟨4166599746378865512482449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22221865314020616066573061 4166599746378865512482449)
                      ·
                        rfl

theorem cell23_8114424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_8114424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114424 prefixEnd_8114424 := by exact prefixLift 8114424
  have htrace : WordTrace (prefixWord ++ tailWord_8114424) baseStart_8114424 baseEnd_8114424 := by
    simpa [prefixWord, tailWord_8114424, baseEnd_8114424] using wordTrace_append hprefix tailTrace_8114424
  have hstable : (prefixWord ++ tailWord_8114424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114424).length < 2 ^ (prefixWord ++ tailWord_8114424).sum := by decide
  have hdescent : baseEnd_8114424 < baseStart_8114424 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114441 : List Nat := [1, 2, 1, 1, 3, 4, 3, 1, 1, 2, 4]
def baseStart_8114441 : Nat := 118140960795 + 8114441 * 2 ^ 59
def prefixEnd_8114441 : Nat := 4983230072969 + 3 ^ 40 * 8114441 * 2
def baseEnd_8114441 : Nat := 4166608475549991945969871

theorem tailTrace_8114441 : CollatzResearch.WordTrace tailWord_8114441 prefixEnd_8114441 4166608475549991945969871 := by
  unfold tailWord_8114441
  simp only [CollatzResearch.WordTrace]
  refine ⟨295957977195773568035855177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197305318130515712023903451 295957977195773568035855177)
  ·
    refine ⟨221968482896830176026891383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295957977195773568035855177 221968482896830176026891383)
    ·
      refine ⟨332952724345245264040337075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221968482896830176026891383 332952724345245264040337075)
      ·
        refine ⟨499429086517867896060505613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332952724345245264040337075 499429086517867896060505613)
        ·
          refine ⟨187285907444200461022689605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 499429086517867896060505613 187285907444200461022689605)
          ·
            refine ⟨35116107645787586441754301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187285907444200461022689605 35116107645787586441754301)
            ·
              refine ⟨13168540367170344915657863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35116107645787586441754301 13168540367170344915657863)
              ·
                refine ⟨19752810550755517373486795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13168540367170344915657863 19752810550755517373486795)
                ·
                  refine ⟨29629215826133276060230193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19752810550755517373486795 29629215826133276060230193)
                  ·
                    refine ⟨22221911869599957045172645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29629215826133276060230193 22221911869599957045172645)
                    ·
                      refine ⟨4166608475549991945969871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22221911869599957045172645 4166608475549991945969871)
                      ·
                        rfl

theorem cell23_8114441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 2, 4].length) (baseStart_8114441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114441 prefixEnd_8114441 := by exact prefixLift 8114441
  have htrace : WordTrace (prefixWord ++ tailWord_8114441) baseStart_8114441 baseEnd_8114441 := by
    simpa [prefixWord, tailWord_8114441, baseEnd_8114441] using wordTrace_append hprefix tailTrace_8114441
  have hstable : (prefixWord ++ tailWord_8114441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114441).length < 2 ^ (prefixWord ++ tailWord_8114441).sum := by decide
  have hdescent : baseEnd_8114441 < baseStart_8114441 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114531 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 4]
def baseStart_8114531 : Nat := 118140960795 + 8114531 * 2 ^ 59
def prefixEnd_8114531 : Nat := 4983230072969 + 3 ^ 40 * 8114531 * 2
def baseEnd_8114531 : Nat := 4166654688808896593844457

theorem tailTrace_8114531 : CollatzResearch.WordTrace tailWord_8114531 prefixEnd_8114531 4166654688808896593844457 := by
  unfold tailWord_8114531
  simp only [CollatzResearch.WordTrace]
  refine ⟨295961259765447513406631447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197307506510298342271087631 295961259765447513406631447)
  ·
    refine ⟨443941889648171270109947171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295961259765447513406631447 443941889648171270109947171)
    ·
      refine ⟨665912834472256905164920757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443941889648171270109947171 665912834472256905164920757)
      ·
        refine ⟨62429328231774084859211321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 665912834472256905164920757 62429328231774084859211321)
        ·
          refine ⟨46821996173830563644408491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62429328231774084859211321 46821996173830563644408491)
          ·
            refine ⟨70232994260745845466612737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46821996173830563644408491 70232994260745845466612737)
            ·
              refine ⟨52674745695559384099959553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70232994260745845466612737 52674745695559384099959553)
              ·
                refine ⟨39506059271669538074969665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52674745695559384099959553 39506059271669538074969665)
                ·
                  refine ⟨29629544453752153556227249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39506059271669538074969665 29629544453752153556227249)
                  ·
                    refine ⟨22222158340314115167170437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29629544453752153556227249 22222158340314115167170437)
                    ·
                      refine ⟨4166654688808896593844457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22222158340314115167170437 4166654688808896593844457)
                      ·
                        rfl

theorem cell23_8114531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_8114531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114531 prefixEnd_8114531 := by exact prefixLift 8114531
  have htrace : WordTrace (prefixWord ++ tailWord_8114531) baseStart_8114531 baseEnd_8114531 := by
    simpa [prefixWord, tailWord_8114531, baseEnd_8114531] using wordTrace_append hprefix tailTrace_8114531
  have hstable : (prefixWord ++ tailWord_8114531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114531).length < 2 ^ (prefixWord ++ tailWord_8114531).sum := by decide
  have hdescent : baseEnd_8114531 < baseStart_8114531 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114538 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_8114538 : Nat := 118140960795 + 8114538 * 2 ^ 59
def prefixEnd_8114538 : Nat := 4983230072969 + 3 ^ 40 * 8114538 * 2
def baseEnd_8114538 : Nat := 4166658283173478066456925

theorem tailTrace_8114538 : CollatzResearch.WordTrace tailWord_8114538 prefixEnd_8114538 4166658283173478066456925 := by
  unfold tailWord_8114538
  simp only [CollatzResearch.WordTrace]
  refine ⟨73990378769105538400534067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197307676717614769068090845 73990378769105538400534067)
  ·
    refine ⟨110985568153658307600801101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73990378769105538400534067 110985568153658307600801101)
    ·
      refine ⟨41619588057621865350300413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110985568153658307600801101 41619588057621865350300413)
      ·
        refine ⟨15607345521608199506362655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41619588057621865350300413 15607345521608199506362655)
        ·
          refine ⟨23411018282412299259543983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15607345521608199506362655 23411018282412299259543983)
          ·
            refine ⟨35116527423618448889315975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23411018282412299259543983 35116527423618448889315975)
            ·
              refine ⟨52674791135427673333973963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35116527423618448889315975 52674791135427673333973963)
              ·
                refine ⟨79012186703141510000960945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52674791135427673333973963 79012186703141510000960945)
                ·
                  refine ⟨59259140027356132500720709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79012186703141510000960945 59259140027356132500720709)
                  ·
                    refine ⟨11111088755129274843885133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59259140027356132500720709 11111088755129274843885133)
                    ·
                      refine ⟨4166658283173478066456925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11111088755129274843885133 4166658283173478066456925)
                      ·
                        rfl

theorem cell23_8114538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_8114538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114538 prefixEnd_8114538 := by exact prefixLift 8114538
  have htrace : WordTrace (prefixWord ++ tailWord_8114538) baseStart_8114538 baseEnd_8114538 := by
    simpa [prefixWord, tailWord_8114538, baseEnd_8114538] using wordTrace_append hprefix tailTrace_8114538
  have hstable : (prefixWord ++ tailWord_8114538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114538).length < 2 ^ (prefixWord ++ tailWord_8114538).sum := by decide
  have hdescent : baseEnd_8114538 < baseStart_8114538 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114541 : List Nat := [1, 5, 1, 1, 1, 2, 2, 3, 7]
def baseStart_8114541 : Nat := 118140960795 + 8114541 * 2 ^ 59
def prefixEnd_8114541 : Nat := 4983230072969 + 3 ^ 40 * 8114541 * 2
def baseEnd_8114541 : Nat := 462962202623937950524379

theorem tailTrace_8114541 : CollatzResearch.WordTrace tailWord_8114541 prefixEnd_8114541 462962202623937950524379 := by
  unfold tailWord_8114541
  simp only [CollatzResearch.WordTrace]
  refine ⟨295961624495411285114495477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197307749663607523409663651 295961624495411285114495477)
  ·
    refine ⟨27746402296444807979483951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295961624495411285114495477 27746402296444807979483951)
    ·
      refine ⟨41619603444667211969225927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27746402296444807979483951 41619603444667211969225927)
      ·
        refine ⟨62429405167000817953838891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41619603444667211969225927 62429405167000817953838891)
        ·
          refine ⟨93644107750501226930758337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62429405167000817953838891 93644107750501226930758337)
          ·
            refine ⟨70233080812875920198068753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93644107750501226930758337 70233080812875920198068753)
            ·
              refine ⟨52674810609656940148551565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70233080812875920198068753 52674810609656940148551565)
              ·
                refine ⟨19753053978621352555706837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52674810609656940148551565 19753053978621352555706837)
                ·
                  refine ⟨462962202623937950524379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19753053978621352555706837 462962202623937950524379)
                  ·
                    rfl

theorem cell23_8114541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_8114541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114541 prefixEnd_8114541 := by exact prefixLift 8114541
  have htrace : WordTrace (prefixWord ++ tailWord_8114541) baseStart_8114541 baseEnd_8114541 := by
    simpa [prefixWord, tailWord_8114541, baseEnd_8114541] using wordTrace_append hprefix tailTrace_8114541
  have hstable : (prefixWord ++ tailWord_8114541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114541).length < 2 ^ (prefixWord ++ tailWord_8114541).sum := by decide
  have hdescent : baseEnd_8114541 < baseStart_8114541 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114571 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 1, 7]
def baseStart_8114571 : Nat := 118140960795 + 8114571 * 2 ^ 59
def prefixEnd_8114571 : Nat := 4983230072969 + 3 ^ 40 * 8114571 * 2
def baseEnd_8114571 : Nat := 1388891742678358812448091

theorem tailTrace_8114571 : CollatzResearch.WordTrace tailWord_8114571 prefixEnd_8114571 1388891742678358812448091 := by
  unfold tailWord_8114571
  simp only [CollatzResearch.WordTrace]
  refine ⟨295962718685302600238087567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197308479123535066825391711 295962718685302600238087567)
  ·
    refine ⟨443944078027953900357131351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295962718685302600238087567 443944078027953900357131351)
    ·
      refine ⟨665916117041930850535697027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443944078027953900357131351 665916117041930850535697027)
      ·
        refine ⟨998874175562896275803545541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665916117041930850535697027 998874175562896275803545541)
        ·
          refine ⟨187288907918043051713164789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 998874175562896275803545541 187288907918043051713164789)
          ·
            refine ⟨17558335117316536098109199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187288907918043051713164789 17558335117316536098109199)
            ·
              refine ⟨26337502675974804147163799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17558335117316536098109199 26337502675974804147163799)
              ·
                refine ⟨39506254013962206220745699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26337502675974804147163799 39506254013962206220745699)
                ·
                  refine ⟨59259381020943309331118549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39506254013962206220745699 59259381020943309331118549)
                  ·
                    refine ⟨1388891742678358812448091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59259381020943309331118549 1388891742678358812448091)
                    ·
                      rfl

theorem cell23_8114571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 7].length) (baseStart_8114571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114571 prefixEnd_8114571 := by exact prefixLift 8114571
  have htrace : WordTrace (prefixWord ++ tailWord_8114571) baseStart_8114571 baseEnd_8114571 := by
    simpa [prefixWord, tailWord_8114571, baseEnd_8114571] using wordTrace_append hprefix tailTrace_8114571
  have hstable : (prefixWord ++ tailWord_8114571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114571).length < 2 ^ (prefixWord ++ tailWord_8114571).sum := by decide
  have hdescent : baseEnd_8114571 < baseStart_8114571 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114631 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 8]
def baseStart_8114631 : Nat := 118140960795 + 8114631 * 2 ^ 59
def prefixEnd_8114631 : Nat := 4983230072969 + 3 ^ 40 * 8114631 * 2
def baseEnd_8114631 : Nat := 462967337430482911399333

theorem tailTrace_8114631 : CollatzResearch.WordTrace tailWord_8114631 prefixEnd_8114631 462967337430482911399333 := by
  unfold tailWord_8114631
  simp only [CollatzResearch.WordTrace]
  refine ⟨295964907065085230485271747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197309938043390153656847831 295964907065085230485271747)
  ·
    refine ⟨443947360597627845727907621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295964907065085230485271747 443947360597627845727907621)
    ·
      refine ⟨83240130112055221073982679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 443947360597627845727907621 83240130112055221073982679)
      ·
        refine ⟨124860195168082831610974019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83240130112055221073982679 124860195168082831610974019)
        ·
          refine ⟨187290292752124247416461029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124860195168082831610974019 187290292752124247416461029)
          ·
            refine ⟨35116929891023296390586443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187290292752124247416461029 35116929891023296390586443)
            ·
              refine ⟨52675394836534944585879665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35116929891023296390586443 52675394836534944585879665)
              ·
                refine ⟨39506546127401208439409749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52675394836534944585879665 39506546127401208439409749)
                ·
                  refine ⟨462967337430482911399333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39506546127401208439409749 462967337430482911399333)
                  ·
                    rfl

theorem cell23_8114631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 8].length) (baseStart_8114631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114631 prefixEnd_8114631 := by exact prefixLift 8114631
  have htrace : WordTrace (prefixWord ++ tailWord_8114631) baseStart_8114631 baseEnd_8114631 := by
    simpa [prefixWord, tailWord_8114631, baseEnd_8114631] using wordTrace_append hprefix tailTrace_8114631
  have hstable : (prefixWord ++ tailWord_8114631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114631).length < 2 ^ (prefixWord ++ tailWord_8114631).sum := by decide
  have hdescent : baseEnd_8114631 < baseStart_8114631 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114642 : List Nat := [3, 2, 2, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_8114642 : Nat := 118140960795 + 8114642 * 2 ^ 59
def prefixEnd_8114642 : Nat := 4983230072969 + 3 ^ 40 * 8114642 * 2
def baseEnd_8114642 : Nat := 4166711685161545659556447

theorem tailTrace_8114642 : CollatzResearch.WordTrace tailWord_8114642 prefixEnd_8114642 4166711685161545659556447 := by
  unfold tailWord_8114642
  simp only [CollatzResearch.WordTrace]
  refine ⟨73991327067011344840980545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197310205512030252909281453 73991327067011344840980545)
  ·
    refine ⟨55493495300258508630735409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73991327067011344840980545 55493495300258508630735409)
    ·
      refine ⟨41620121475193881473051557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55493495300258508630735409 41620121475193881473051557)
      ·
        refine ⟨7803772776598852776197167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41620121475193881473051557 7803772776598852776197167)
        ·
          refine ⟨11705659164898279164295751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7803772776598852776197167 11705659164898279164295751)
          ·
            refine ⟨17558488747347418746443627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11705659164898279164295751 17558488747347418746443627)
            ·
              refine ⟨26337733121021128119665441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17558488747347418746443627 26337733121021128119665441)
              ·
                refine ⟨19753299840765846089749081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26337733121021128119665441 19753299840765846089749081)
                ·
                  refine ⟨14814974880574384567311811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19753299840765846089749081 14814974880574384567311811)
                  ·
                    refine ⟨22222462320861576850967717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14814974880574384567311811 22222462320861576850967717)
                    ·
                      refine ⟨4166711685161545659556447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22222462320861576850967717 4166711685161545659556447)
                      ·
                        rfl

theorem cell23_8114642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_8114642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114642 prefixEnd_8114642 := by exact prefixLift 8114642
  have htrace : WordTrace (prefixWord ++ tailWord_8114642) baseStart_8114642 baseEnd_8114642 := by
    simpa [prefixWord, tailWord_8114642, baseEnd_8114642] using wordTrace_append hprefix tailTrace_8114642
  have hstable : (prefixWord ++ tailWord_8114642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114642).length < 2 ^ (prefixWord ++ tailWord_8114642).sum := by decide
  have hdescent : baseEnd_8114642 < baseStart_8114642 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114645 : List Nat := [1, 3, 2, 3, 1, 3, 1, 2, 2, 2, 3]
def baseStart_8114645 : Nat := 118140960795 + 8114645 * 2 ^ 59
def prefixEnd_8114645 : Nat := 4983230072969 + 3 ^ 40 * 8114645 * 2
def baseEnd_8114645 : Nat := 4166713225603509147818933

theorem tailTrace_8114645 : CollatzResearch.WordTrace tailWord_8114645 prefixEnd_8114645 4166713225603509147818933 := by
  unfold tailWord_8114645
  simp only [CollatzResearch.WordTrace]
  refine ⟨295965417687034510876281389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197310278458023007250854259 295965417687034510876281389)
  ·
    refine ⟨110987031632637941578605521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295965417687034510876281389 110987031632637941578605521)
    ·
      refine ⟨83240273724478456183954141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110987031632637941578605521 83240273724478456183954141)
      ·
        refine ⟨31215102646679421068982803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83240273724478456183954141 31215102646679421068982803)
        ·
          refine ⟨46822653970019131603474205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31215102646679421068982803 46822653970019131603474205)
          ·
            refine ⟨17558495238757174351302827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46822653970019131603474205 17558495238757174351302827)
            ·
              refine ⟨26337742858135761526954241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17558495238757174351302827 26337742858135761526954241)
              ·
                refine ⟨19753307143601821145215681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26337742858135761526954241 19753307143601821145215681)
                ·
                  refine ⟨14814980357701365858911761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19753307143601821145215681 14814980357701365858911761)
                  ·
                    refine ⟨11111235268276024394183821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14814980357701365858911761 11111235268276024394183821)
                    ·
                      refine ⟨4166713225603509147818933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11111235268276024394183821 4166713225603509147818933)
                      ·
                        rfl

theorem cell23_8114645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_8114645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114645 prefixEnd_8114645 := by exact prefixLift 8114645
  have htrace : WordTrace (prefixWord ++ tailWord_8114645) baseStart_8114645 baseEnd_8114645 := by
    simpa [prefixWord, tailWord_8114645, baseEnd_8114645] using wordTrace_append hprefix tailTrace_8114645
  have hstable : (prefixWord ++ tailWord_8114645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114645).length < 2 ^ (prefixWord ++ tailWord_8114645).sum := by decide
  have hdescent : baseEnd_8114645 < baseStart_8114645 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114702 : List Nat := [4, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2]
def baseStart_8114702 : Nat := 118140960795 + 8114702 * 2 ^ 59
def prefixEnd_8114702 : Nat := 4983230072969 + 3 ^ 40 * 8114702 * 2
def baseEnd_8114702 : Nat := 4166742494000815424806171

theorem tailTrace_8114702 : CollatzResearch.WordTrace tailWord_8114702 prefixEnd_8114702 4166742494000815424806171 := by
  unfold tailWord_8114702
  simp only [CollatzResearch.WordTrace]
  refine ⟨36995937080978501201388295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197311664431885339740737573 36995937080978501201388295)
  ·
    refine ⟨55493905621467751802082443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36995937080978501201388295 55493905621467751802082443)
    ·
      refine ⟨83240858432201627703123665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55493905621467751802082443 83240858432201627703123665)
      ·
        refine ⟨62430643824151220777342749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83240858432201627703123665 62430643824151220777342749)
        ·
          refine ⟨23411491434056707791503531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62430643824151220777342749 23411491434056707791503531)
          ·
            refine ⟨35117237151085061687255297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23411491434056707791503531 35117237151085061687255297)
            ·
              refine ⟨26337927863313796265441473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35117237151085061687255297 26337927863313796265441473)
              ·
                refine ⟨19753445897485347199081105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26337927863313796265441473 19753445897485347199081105)
                ·
                  refine ⟨14815084423114010399310829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19753445897485347199081105 14815084423114010399310829)
                  ·
                    refine ⟨5555656658667753899741561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14815084423114010399310829 5555656658667753899741561)
                    ·
                      refine ⟨4166742494000815424806171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5555656658667753899741561 4166742494000815424806171)
                      ·
                        rfl

theorem cell23_8114702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_8114702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114702 prefixEnd_8114702 := by exact prefixLift 8114702
  have htrace : WordTrace (prefixWord ++ tailWord_8114702) baseStart_8114702 baseEnd_8114702 := by
    simpa [prefixWord, tailWord_8114702, baseEnd_8114702] using wordTrace_append hprefix tailTrace_8114702
  have hstable : (prefixWord ++ tailWord_8114702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114702).length < 2 ^ (prefixWord ++ tailWord_8114702).sum := by decide
  have hdescent : baseEnd_8114702 < baseStart_8114702 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114715 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 9, 2, 2]
def baseStart_8114715 : Nat := 118140960795 + 8114715 * 2 ^ 59
def prefixEnd_8114715 : Nat := 4983230072969 + 3 ^ 40 * 8114715 * 2
def baseEnd_8114715 : Nat := 4166749169249323873943611

theorem tailTrace_8114715 : CollatzResearch.WordTrace tailWord_8114715 prefixEnd_8114715 4166749169249323873943611 := by
  unfold tailWord_8114715
  simp only [CollatzResearch.WordTrace]
  refine ⟨295967970796780912831329599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197311980531187275220886399 295967970796780912831329599)
  ·
    refine ⟨443951956195171369246994399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295967970796780912831329599 443951956195171369246994399)
    ·
      refine ⟨665927934292757053870491599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443951956195171369246994399 665927934292757053870491599)
      ·
        refine ⟨998891901439135580805737399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665927934292757053870491599 998891901439135580805737399)
        ·
          refine ⟨1498337852158703371208606099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998891901439135580805737399 1498337852158703371208606099)
          ·
            refine ⟨2247506778238055056812909149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1498337852158703371208606099 2247506778238055056812909149)
            ·
              refine ⟨842815041839270646304840931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2247506778238055056812909149 842815041839270646304840931)
              ·
                refine ⟨1264222562758905969457261397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842815041839270646304840931 1264222562758905969457261397)
                ·
                  refine ⟨7407554078665464664788641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1264222562758905969457261397 7407554078665464664788641)
                  ·
                    refine ⟨5555665558999098498591481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7407554078665464664788641 5555665558999098498591481)
                    ·
                      refine ⟨4166749169249323873943611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5555665558999098498591481 4166749169249323873943611)
                      ·
                        rfl

theorem cell23_8114715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 2, 2].length) (baseStart_8114715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114715 prefixEnd_8114715 := by exact prefixLift 8114715
  have htrace : WordTrace (prefixWord ++ tailWord_8114715) baseStart_8114715 baseEnd_8114715 := by
    simpa [prefixWord, tailWord_8114715, baseEnd_8114715] using wordTrace_append hprefix tailTrace_8114715
  have hstable : (prefixWord ++ tailWord_8114715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114715).length < 2 ^ (prefixWord ++ tailWord_8114715).sum := by decide
  have hdescent : baseEnd_8114715 < baseStart_8114715 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114725 : List Nat := [1, 3, 1, 2, 2, 1, 4, 3, 2, 4]
def baseStart_8114725 : Nat := 118140960795 + 8114725 * 2 ^ 59
def prefixEnd_8114725 : Nat := 4983230072969 + 3 ^ 40 * 8114725 * 2
def baseEnd_8114725 : Nat := 1388918101351956278272855

theorem tailTrace_8114725 : CollatzResearch.WordTrace tailWord_8114725 prefixEnd_8114725 1388918101351956278272855 := by
  unfold tailWord_8114725
  simp only [CollatzResearch.WordTrace]
  refine ⟨295968335526744684539193629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197312223684496456359462419 295968335526744684539193629)
  ·
    refine ⟨110988125822529256702197611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295968335526744684539193629 110988125822529256702197611)
    ·
      refine ⟨166482188733793885053296417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110988125822529256702197611 166482188733793885053296417)
      ·
        refine ⟨124861641550345413789972313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166482188733793885053296417 124861641550345413789972313)
        ·
          refine ⟨93646231162759060342479235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124861641550345413789972313 93646231162759060342479235)
          ·
            refine ⟨140469346744138590513718853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93646231162759060342479235 140469346744138590513718853)
            ·
              refine ⟨26338002514525985721322285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140469346744138590513718853 26338002514525985721322285)
              ·
                refine ⟨9876750942947244645495857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26338002514525985721322285 9876750942947244645495857)
                ·
                  refine ⟨7407563207210433484121893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9876750942947244645495857 7407563207210433484121893)
                  ·
                    refine ⟨1388918101351956278272855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7407563207210433484121893 1388918101351956278272855)
                    ·
                      rfl

theorem cell23_8114725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_8114725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114725 prefixEnd_8114725 := by exact prefixLift 8114725
  have htrace : WordTrace (prefixWord ++ tailWord_8114725) baseStart_8114725 baseEnd_8114725 := by
    simpa [prefixWord, tailWord_8114725, baseEnd_8114725] using wordTrace_append hprefix tailTrace_8114725
  have hstable : (prefixWord ++ tailWord_8114725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114725).length < 2 ^ (prefixWord ++ tailWord_8114725).sum := by decide
  have hdescent : baseEnd_8114725 < baseStart_8114725 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114731 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 7]
def baseStart_8114731 : Nat := 118140960795 + 8114731 * 2 ^ 59
def prefixEnd_8114731 : Nat := 4983230072969 + 3 ^ 40 * 8114731 * 2
def baseEnd_8114731 : Nat := 4166757384939795811343537

theorem tailTrace_8114731 : CollatzResearch.WordTrace tailWord_8114731 prefixEnd_8114731 4166757384939795811343537 := by
  unfold tailWord_8114731
  simp only [CollatzResearch.WordTrace]
  refine ⟨295968554364722947563912047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197312369576481965042608031 295968554364722947563912047)
  ·
    refine ⟨443952831547084421345868071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295968554364722947563912047 443952831547084421345868071)
    ·
      refine ⟨665929247320626632018802107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443952831547084421345868071 665929247320626632018802107)
      ·
        refine ⟨998893870980939948028203161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665929247320626632018802107 998893870980939948028203161)
        ·
          refine ⟨749170403235704961021152371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 998893870980939948028203161 749170403235704961021152371)
          ·
            refine ⟨1123755604853557441531728557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749170403235704961021152371 1123755604853557441531728557)
            ·
              refine ⟨421408351820084040574398209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1123755604853557441531728557 421408351820084040574398209)
              ·
                refine ⟨316056263865063030430798657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421408351820084040574398209 316056263865063030430798657)
                ·
                  refine ⟨237042197898797272823098993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316056263865063030430798657 237042197898797272823098993)
                  ·
                    refine ⟨177781648424097954617324245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 237042197898797272823098993 177781648424097954617324245)
                    ·
                      refine ⟨4166757384939795811343537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177781648424097954617324245 4166757384939795811343537)
                      ·
                        rfl

theorem cell23_8114731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 7].length) (baseStart_8114731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114731 prefixEnd_8114731 := by exact prefixLift 8114731
  have htrace : WordTrace (prefixWord ++ tailWord_8114731) baseStart_8114731 baseEnd_8114731 := by
    simpa [prefixWord, tailWord_8114731, baseEnd_8114731] using wordTrace_append hprefix tailTrace_8114731
  have hstable : (prefixWord ++ tailWord_8114731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114731).length < 2 ^ (prefixWord ++ tailWord_8114731).sum := by decide
  have hdescent : baseEnd_8114731 < baseStart_8114731 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114749 : List Nat := [1, 4, 1, 3, 2, 3, 2, 1, 1, 1, 4]
def baseStart_8114749 : Nat := 118140960795 + 8114749 * 2 ^ 59
def prefixEnd_8114749 : Nat := 4983230072969 + 3 ^ 40 * 8114749 * 2
def baseEnd_8114749 : Nat := 4166766627591576740918455

theorem tailTrace_8114749 : CollatzResearch.WordTrace tailWord_8114749 prefixEnd_8114749 4166766627591576740918455 := by
  unfold tailWord_8114749
  simp only [CollatzResearch.WordTrace]
  refine ⟨295969210878657736638067301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197312807252438491092044867 295969210878657736638067301)
  ·
    refine ⟨55494227039748325619637619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295969210878657736638067301 55494227039748325619637619)
    ·
      refine ⟨83241340559622488429456429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55494227039748325619637619 83241340559622488429456429)
      ·
        refine ⟨31215502709858433161046161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83241340559622488429456429 31215502709858433161046161)
        ·
          refine ⟨23411627032393824870784621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31215502709858433161046161 23411627032393824870784621)
          ·
            refine ⟨8779360137147684326544233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23411627032393824870784621 8779360137147684326544233)
            ·
              refine ⟨6584520102860763244908175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8779360137147684326544233 6584520102860763244908175)
              ·
                refine ⟨9876780154291144867362263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6584520102860763244908175 9876780154291144867362263)
                ·
                  refine ⟨14815170231436717301043395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9876780154291144867362263 14815170231436717301043395)
                  ·
                    refine ⟨22222755347155075951565093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14815170231436717301043395 22222755347155075951565093)
                    ·
                      refine ⟨4166766627591576740918455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22222755347155075951565093 4166766627591576740918455)
                      ·
                        rfl

theorem cell23_8114749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_8114749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114749 prefixEnd_8114749 := by exact prefixLift 8114749
  have htrace : WordTrace (prefixWord ++ tailWord_8114749) baseStart_8114749 baseEnd_8114749 := by
    simpa [prefixWord, tailWord_8114749, baseEnd_8114749] using wordTrace_append hprefix tailTrace_8114749
  have hstable : (prefixWord ++ tailWord_8114749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114749).length < 2 ^ (prefixWord ++ tailWord_8114749).sum := by decide
  have hdescent : baseEnd_8114749 < baseStart_8114749 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114752 : List Nat := [2, 1, 1, 2, 2, 2, 6, 1, 1, 2, 3]
def baseStart_8114752 : Nat := 118140960795 + 8114752 * 2 ^ 59
def prefixEnd_8114752 : Nat := 4983230072969 + 3 ^ 40 * 8114752 * 2
def baseEnd_8114752 : Nat := 4166768168033540229180941

theorem tailTrace_8114752 : CollatzResearch.WordTrace tailWord_8114752 prefixEnd_8114752 4166768168033540229180941 := by
  unfold tailWord_8114752
  simp only [CollatzResearch.WordTrace]
  refine ⟨147984660148823434075213255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197312880198431245433617673 147984660148823434075213255)
  ·
    refine ⟨221976990223235151112819883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147984660148823434075213255 221976990223235151112819883)
    ·
      refine ⟨332965485334852726669229825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221976990223235151112819883 332965485334852726669229825)
      ·
        refine ⟨249724114001139545001922369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332965485334852726669229825 249724114001139545001922369)
        ·
          refine ⟨187293085500854658751441777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249724114001139545001922369 187293085500854658751441777)
          ·
            refine ⟨140469814125640994063581333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187293085500854658751441777 140469814125640994063581333)
            ·
              refine ⟨6584522537139421596730375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 140469814125640994063581333 6584522537139421596730375)
              ·
                refine ⟨9876783805709132395095563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6584522537139421596730375 9876783805709132395095563)
                ·
                  refine ⟨14815175708563698592643345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9876783805709132395095563 14815175708563698592643345)
                  ·
                    refine ⟨11111381781422773944482509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14815175708563698592643345 11111381781422773944482509)
                    ·
                      refine ⟨4166768168033540229180941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11111381781422773944482509 4166768168033540229180941)
                      ·
                        rfl

theorem cell23_8114752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 1, 2, 3].length) (baseStart_8114752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114752 prefixEnd_8114752 := by exact prefixLift 8114752
  have htrace : WordTrace (prefixWord ++ tailWord_8114752) baseStart_8114752 baseEnd_8114752 := by
    simpa [prefixWord, tailWord_8114752, baseEnd_8114752] using wordTrace_append hprefix tailTrace_8114752
  have hstable : (prefixWord ++ tailWord_8114752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114752).length < 2 ^ (prefixWord ++ tailWord_8114752).sum := by decide
  have hdescent : baseEnd_8114752 < baseStart_8114752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114786 : List Nat := [3, 3, 2, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_8114786 : Nat := 118140960795 + 8114786 * 2 ^ 59
def prefixEnd_8114786 : Nat := 4983230072969 + 3 ^ 40 * 8114786 * 2
def baseEnd_8114786 : Nat := 4166785626375793096155785

theorem tailTrace_8114786 : CollatzResearch.WordTrace tailWord_8114786 prefixEnd_8114786 4166785626375793096155785 := by
  unfold tailWord_8114786
  simp only [CollatzResearch.WordTrace]
  refine ⟨73992640094880922989291053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197313706919682461304776141 73992640094880922989291053)
  ·
    refine ⟨27747240035580346120984145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73992640094880922989291053 27747240035580346120984145)
    ·
      refine ⟨20810430026685259590738109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27747240035580346120984145 20810430026685259590738109)
      ·
        refine ⟨7803911260006972346526791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20810430026685259590738109 7803911260006972346526791)
        ·
          refine ⟨11705866890010458519790187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7803911260006972346526791 11705866890010458519790187)
          ·
            refine ⟨17558800335015687779685281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11705866890010458519790187 17558800335015687779685281)
            ·
              refine ⟨13169100251261765834763961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17558800335015687779685281 13169100251261765834763961)
              ·
                refine ⟨9876825188446324376072971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13169100251261765834763961 9876825188446324376072971)
                ·
                  refine ⟨14815237782669486564109457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9876825188446324376072971 14815237782669486564109457)
                  ·
                    refine ⟨11111428337002114923082093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14815237782669486564109457 11111428337002114923082093)
                    ·
                      refine ⟨4166785626375793096155785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11111428337002114923082093 4166785626375793096155785)
                      ·
                        rfl

theorem cell23_8114786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_8114786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114786 prefixEnd_8114786 := by exact prefixLift 8114786
  have htrace : WordTrace (prefixWord ++ tailWord_8114786) baseStart_8114786 baseEnd_8114786 := by
    simpa [prefixWord, tailWord_8114786, baseEnd_8114786] using wordTrace_append hprefix tailTrace_8114786
  have hstable : (prefixWord ++ tailWord_8114786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114786).length < 2 ^ (prefixWord ++ tailWord_8114786).sum := by decide
  have hdescent : baseEnd_8114786 < baseStart_8114786 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114808 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 2, 1, 5]
def baseStart_8114808 : Nat := 118140960795 + 8114808 * 2 ^ 59
def prefixEnd_8114808 : Nat := 4983230072969 + 3 ^ 40 * 8114808 * 2
def baseEnd_8114808 : Nat := 4166796922950192010080683

theorem tailTrace_8114808 : CollatzResearch.WordTrace tailWord_8114808 prefixEnd_8114808 4166796922950192010080683 := by
  unfold tailWord_8114808
  simp only [CollatzResearch.WordTrace]
  refine ⟨147985681392721994857232539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197314241856962659809643385 147985681392721994857232539)
  ·
    refine ⟨221978522089082992285848809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147985681392721994857232539 221978522089082992285848809)
    ·
      refine ⟨166483891566812244214386607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221978522089082992285848809 166483891566812244214386607)
      ·
        refine ⟨249725837350218366321579911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166483891566812244214386607 249725837350218366321579911)
        ·
          refine ⟨374588756025327549482369867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249725837350218366321579911 374588756025327549482369867)
          ·
            refine ⟨561883134037991324223554801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374588756025327549482369867 561883134037991324223554801)
            ·
              refine ⟨421412350528493493167666101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561883134037991324223554801 421412350528493493167666101)
              ·
                refine ⟨39507407862046264984468697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 421412350528493493167666101 39507407862046264984468697)
                ·
                  refine ⟨29630555896534698738351523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39507407862046264984468697 29630555896534698738351523)
                  ·
                    refine ⟨44445833844802048107527285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29630555896534698738351523 44445833844802048107527285)
                    ·
                      refine ⟨4166796922950192010080683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44445833844802048107527285 4166796922950192010080683)
                      ·
                        rfl

theorem cell23_8114808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_8114808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114808 prefixEnd_8114808 := by exact prefixLift 8114808
  have htrace : WordTrace (prefixWord ++ tailWord_8114808) baseStart_8114808 baseEnd_8114808 := by
    simpa [prefixWord, tailWord_8114808, baseEnd_8114808] using wordTrace_append hprefix tailTrace_8114808
  have hstable : (prefixWord ++ tailWord_8114808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114808).length < 2 ^ (prefixWord ++ tailWord_8114808).sum := by decide
  have hdescent : baseEnd_8114808 < baseStart_8114808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114828 : List Nat := [2, 2, 1, 2, 1, 1, 2, 5, 7]
def baseStart_8114828 : Nat := 118140960795 + 8114828 * 2 ^ 59
def prefixEnd_8114828 : Nat := 4983230072969 + 3 ^ 40 * 8114828 * 2
def baseEnd_8114828 : Nat := 462978576951475770203399

theorem tailTrace_8114828 : CollatzResearch.WordTrace tailWord_8114828 prefixEnd_8114828 462978576951475770203399 := by
  unfold tailWord_8114828
  simp only [CollatzResearch.WordTrace]
  refine ⟨147986046122685766565096569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197314728163581022086795425 147986046122685766565096569)
  ·
    refine ⟨110989534592014324923822427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147986046122685766565096569 110989534592014324923822427)
    ·
      refine ⟨166484301888021487385733641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110989534592014324923822427 166484301888021487385733641)
      ·
        refine ⟨124863226416016115539300231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166484301888021487385733641 124863226416016115539300231)
        ·
          refine ⟨187294839624024173308950347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124863226416016115539300231 187294839624024173308950347)
          ·
            refine ⟨280942259436036259963425521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187294839624024173308950347 280942259436036259963425521)
            ·
              refine ⟨210706694577027194972569141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280942259436036259963425521 210706694577027194972569141)
              ·
                refine ⟨19753752616596299528678357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210706694577027194972569141 19753752616596299528678357)
                ·
                  refine ⟨462978576951475770203399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19753752616596299528678357 462978576951475770203399)
                  ·
                    rfl

theorem cell23_8114828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 7].length) (baseStart_8114828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114828 prefixEnd_8114828 := by exact prefixLift 8114828
  have htrace : WordTrace (prefixWord ++ tailWord_8114828) baseStart_8114828 baseEnd_8114828 := by
    simpa [prefixWord, tailWord_8114828, baseEnd_8114828] using wordTrace_append hprefix tailTrace_8114828
  have hstable : (prefixWord ++ tailWord_8114828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114828).length < 2 ^ (prefixWord ++ tailWord_8114828).sum := by decide
  have hdescent : baseEnd_8114828 < baseStart_8114828 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114839 : List Nat := [1, 1, 3, 3, 2, 1, 3, 3, 2, 2, 2]
def baseStart_8114839 : Nat := 118140960795 + 8114839 * 2 ^ 59
def prefixEnd_8114839 : Nat := 4983230072969 + 3 ^ 40 * 8114839 * 2
def baseEnd_8114839 : Nat := 4166812840850481388793041

theorem tailTrace_8114839 : CollatzResearch.WordTrace tailWord_8114839 prefixEnd_8114839 4166812840850481388793041 := by
  unfold tailWord_8114839
  simp only [CollatzResearch.WordTrace]
  refine ⟨295972493448331682008843571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197314995632221121339229047 295972493448331682008843571)
  ·
    refine ⟨443958740172497523013265357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295972493448331682008843571 443958740172497523013265357)
    ·
      refine ⟨166484527564686571129974509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443958740172497523013265357 166484527564686571129974509)
      ·
        refine ⟨62431697836757464173740441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166484527564686571129974509 62431697836757464173740441)
        ·
          refine ⟨46823773377568098130305331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62431697836757464173740441 46823773377568098130305331)
          ·
            refine ⟨70235660066352147195457997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46823773377568098130305331 70235660066352147195457997)
            ·
              refine ⟨26338372524882055198296749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70235660066352147195457997 26338372524882055198296749)
              ·
                refine ⟨9876889696830770699361281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26338372524882055198296749 9876889696830770699361281)
                ·
                  refine ⟨7407667272623078024520961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9876889696830770699361281 7407667272623078024520961)
                  ·
                    refine ⟨5555750454467308518390721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7407667272623078024520961 5555750454467308518390721)
                    ·
                      refine ⟨4166812840850481388793041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5555750454467308518390721 4166812840850481388793041)
                      ·
                        rfl

theorem cell23_8114839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_8114839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114839 prefixEnd_8114839 := by exact prefixLift 8114839
  have htrace : WordTrace (prefixWord ++ tailWord_8114839) baseStart_8114839 baseEnd_8114839 := by
    simpa [prefixWord, tailWord_8114839, baseEnd_8114839] using wordTrace_append hprefix tailTrace_8114839
  have hstable : (prefixWord ++ tailWord_8114839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114839).length < 2 ^ (prefixWord ++ tailWord_8114839).sum := by decide
  have hdescent : baseEnd_8114839 < baseStart_8114839 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114879 : List Nat := [1, 1, 2, 2, 2, 6, 2, 2, 5]
def baseStart_8114879 : Nat := 118140960795 + 8114879 * 2 ^ 59
def prefixEnd_8114879 : Nat := 4983230072969 + 3 ^ 40 * 8114879 * 2
def baseEnd_8114879 : Nat := 462981486675184581365873

theorem tailTrace_8114879 : CollatzResearch.WordTrace tailWord_8114879 prefixEnd_8114879 462981486675184581365873 := by
  unfold tailWord_8114879
  simp only [CollatzResearch.WordTrace]
  refine ⟨295973952368186768840299691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197315968245457845893533127 295973952368186768840299691)
  ·
    refine ⟨443960928552280153260449537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295973952368186768840299691 443960928552280153260449537)
    ·
      refine ⟨332970696414210114945337153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443960928552280153260449537 332970696414210114945337153)
      ·
        refine ⟨249728022310657586209002865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332970696414210114945337153 249728022310657586209002865)
        ·
          refine ⟨187296016732993189656752149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249728022310657586209002865 187296016732993189656752149)
          ·
            refine ⟨8779500784359055765160257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187296016732993189656752149 8779500784359055765160257)
            ·
              refine ⟨6584625588269291823870193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8779500784359055765160257 6584625588269291823870193)
              ·
                refine ⟨4938469191201968867902645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6584625588269291823870193 4938469191201968867902645)
                ·
                  refine ⟨462981486675184581365873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4938469191201968867902645 462981486675184581365873)
                  ·
                    rfl

theorem cell23_8114879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 5].length) (baseStart_8114879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114879 prefixEnd_8114879 := by exact prefixLift 8114879
  have htrace : WordTrace (prefixWord ++ tailWord_8114879) baseStart_8114879 baseEnd_8114879 := by
    simpa [prefixWord, tailWord_8114879, baseEnd_8114879] using wordTrace_append hprefix tailTrace_8114879
  have hstable : (prefixWord ++ tailWord_8114879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114879).length < 2 ^ (prefixWord ++ tailWord_8114879).sum := by decide
  have hdescent : baseEnd_8114879 < baseStart_8114879 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114886 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_8114886 : Nat := 118140960795 + 8114886 * 2 ^ 59
def prefixEnd_8114886 : Nat := 4983230072969 + 3 ^ 40 * 8114886 * 2
def baseEnd_8114886 : Nat := 4166836974441242704905325

theorem tailTrace_8114886 : CollatzResearch.WordTrace tailWord_8114886 prefixEnd_8114886 4166836974441242704905325 := by
  unfold tailWord_8114886
  simp only [CollatzResearch.WordTrace]
  refine ⟨9249193989973794032368891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 197316138452774272690536341 9249193989973794032368891)
  ·
    refine ⟨13873790984960691048553337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9249193989973794032368891 13873790984960691048553337)
    ·
      refine ⟨10405343238720518286415003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13873790984960691048553337 10405343238720518286415003)
      ·
        refine ⟨15608014858080777429622505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10405343238720518286415003 15608014858080777429622505)
        ·
          refine ⟨11706011143560583072216879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15608014858080777429622505 11706011143560583072216879)
          ·
            refine ⟨17559016715340874608325319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11706011143560583072216879 17559016715340874608325319)
            ·
              refine ⟨26338525073011311912487979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17559016715340874608325319 26338525073011311912487979)
              ·
                refine ⟨39507787609516967868731969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26338525073011311912487979 39507787609516967868731969)
                ·
                  refine ⟨29630840707137725901548977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39507787609516967868731969 29630840707137725901548977)
                  ·
                    refine ⟨22223130530353294426161733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29630840707137725901548977 22223130530353294426161733)
                    ·
                      refine ⟨4166836974441242704905325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22223130530353294426161733 4166836974441242704905325)
                      ·
                        rfl

theorem cell23_8114886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_8114886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114886 prefixEnd_8114886 := by exact prefixLift 8114886
  have htrace : WordTrace (prefixWord ++ tailWord_8114886) baseStart_8114886 baseEnd_8114886 := by
    simpa [prefixWord, tailWord_8114886, baseEnd_8114886] using wordTrace_append hprefix tailTrace_8114886
  have hstable : (prefixWord ++ tailWord_8114886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114886).length < 2 ^ (prefixWord ++ tailWord_8114886).sum := by decide
  have hdescent : baseEnd_8114886 < baseStart_8114886 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8114925 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_8114925 : Nat := 118140960795 + 8114925 * 2 ^ 59
def prefixEnd_8114925 : Nat := 4983230072969 + 3 ^ 40 * 8114925 * 2
def baseEnd_8114925 : Nat := 4166857000186768052317645

theorem tailTrace_8114925 : CollatzResearch.WordTrace tailWord_8114925 prefixEnd_8114925 4166857000186768052317645 := by
  unfold tailWord_8114925
  simp only [CollatzResearch.WordTrace]
  refine ⟨295975630126020118696474229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197317086750680079130982819 295975630126020118696474229)
  ·
    refine ⟨27747715324314386127794459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295975630126020118696474229 27747715324314386127794459)
    ·
      refine ⟨41621572986471579191691689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27747715324314386127794459 41621572986471579191691689)
      ·
        refine ⟨31216179739853684393768767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41621572986471579191691689 31216179739853684393768767)
        ·
          refine ⟨46824269609780526590653151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31216179739853684393768767 46824269609780526590653151)
          ·
            refine ⟨70236404414670789885979727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46824269609780526590653151 70236404414670789885979727)
            ·
              refine ⟨105354606622006184828969591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70236404414670789885979727 105354606622006184828969591)
              ·
                refine ⟨158031909933009277243454387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105354606622006184828969591 158031909933009277243454387)
                ·
                  refine ⟨237047864899513915865181581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158031909933009277243454387 237047864899513915865181581)
                  ·
                    refine ⟨88892949337317718449443093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237047864899513915865181581 88892949337317718449443093)
                    ·
                      refine ⟨4166857000186768052317645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88892949337317718449443093 4166857000186768052317645)
                      ·
                        rfl

theorem cell23_8114925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_8114925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8114925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8114925 prefixEnd_8114925 := by exact prefixLift 8114925
  have htrace : WordTrace (prefixWord ++ tailWord_8114925) baseStart_8114925 baseEnd_8114925 := by
    simpa [prefixWord, tailWord_8114925, baseEnd_8114925] using wordTrace_append hprefix tailTrace_8114925
  have hstable : (prefixWord ++ tailWord_8114925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8114925).length < 2 ^ (prefixWord ++ tailWord_8114925).sum := by decide
  have hdescent : baseEnd_8114925 < baseStart_8114925 := by decide
  rcases family_descends (prefixWord ++ tailWord_8114925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115042 : List Nat := [3, 3, 2, 1, 3, 11]
def baseStart_8115042 : Nat := 118140960795 + 8115042 * 2 ^ 59
def prefixEnd_8115042 : Nat := 4983230072969 + 3 ^ 40 * 8115042 * 2
def baseEnd_8115042 : Nat := 17147806902976724668949

theorem tailTrace_8115042 : CollatzResearch.WordTrace tailWord_8115042 prefixEnd_8115042 17147806902976724668949 := by
  unfold tailWord_8115042
  simp only [CollatzResearch.WordTrace]
  refine ⟨73994974366649061919620845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197319931644397498452322253 73994974366649061919620845)
  ·
    refine ⟨27748115387493398219857817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73994974366649061919620845 27748115387493398219857817)
    ·
      refine ⟨20811086540620048664893363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27748115387493398219857817 20811086540620048664893363)
      ·
        refine ⟨31216629810930072997340045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20811086540620048664893363 31216629810930072997340045)
        ·
          refine ⟨11706236179098777374002517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31216629810930072997340045 11706236179098777374002517)
          ·
            refine ⟨17147806902976724668949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11706236179098777374002517 17147806902976724668949)
            ·
              rfl

theorem cell23_8115042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 11].length) (baseStart_8115042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115042 prefixEnd_8115042 := by exact prefixLift 8115042
  have htrace : WordTrace (prefixWord ++ tailWord_8115042) baseStart_8115042 baseEnd_8115042 := by
    simpa [prefixWord, tailWord_8115042, baseEnd_8115042] using wordTrace_append hprefix tailTrace_8115042
  have hstable : (prefixWord ++ tailWord_8115042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115042).length < 2 ^ (prefixWord ++ tailWord_8115042).sum := by decide
  have hdescent : baseEnd_8115042 < baseStart_8115042 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115052 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 3]
def baseStart_8115052 : Nat := 118140960795 + 8115052 * 2 ^ 59
def prefixEnd_8115052 : Nat := 4983230072969 + 3 ^ 40 * 8115052 * 2
def baseEnd_8115052 : Nat := 4166922212229889055429561

theorem tailTrace_8115052 : CollatzResearch.WordTrace tailWord_8115052 prefixEnd_8115052 4166922212229889055429561 := by
  unfold tailWord_8115052
  simp only [CollatzResearch.WordTrace]
  refine ⟨147990131098280009693173705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197320174797706679590898273 147990131098280009693173705)
  ·
    refine ⟨110992598323710007269880279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147990131098280009693173705 110992598323710007269880279)
    ·
      refine ⟨166488897485565010904820419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110992598323710007269880279 166488897485565010904820419)
      ·
        refine ⟨249733346228347516357230629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166488897485565010904820419 249733346228347516357230629)
        ·
          refine ⟨46825002417815159316980743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249733346228347516357230629 46825002417815159316980743)
          ·
            refine ⟨70237503626722738975471115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46825002417815159316980743 70237503626722738975471115)
            ·
              refine ⟨105356255440084108463206673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70237503626722738975471115 105356255440084108463206673)
              ·
                refine ⟨79017191580063081347405005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105356255440084108463206673 79017191580063081347405005)
                ·
                  refine ⟨29631446842523655505276877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79017191580063081347405005 29631446842523655505276877)
                  ·
                    refine ⟨11111792565946370814478829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29631446842523655505276877 11111792565946370814478829)
                    ·
                      refine ⟨4166922212229889055429561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11111792565946370814478829 4166922212229889055429561)
                      ·
                        rfl

theorem cell23_8115052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_8115052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115052 prefixEnd_8115052 := by exact prefixLift 8115052
  have htrace : WordTrace (prefixWord ++ tailWord_8115052) baseStart_8115052 baseEnd_8115052 := by
    simpa [prefixWord, tailWord_8115052, baseEnd_8115052] using wordTrace_append hprefix tailTrace_8115052
  have hstable : (prefixWord ++ tailWord_8115052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115052).length < 2 ^ (prefixWord ++ tailWord_8115052).sum := by decide
  have hdescent : baseEnd_8115052 < baseStart_8115052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115070 : List Nat := [4, 2, 3, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_8115070 : Nat := 118140960795 + 8115070 * 2 ^ 59
def prefixEnd_8115070 : Nat := 4983230072969 + 3 ^ 40 * 8115070 * 2
def baseEnd_8115070 : Nat := 4166931454881669985004479

theorem tailTrace_8115070 : CollatzResearch.WordTrace tailWord_8115070 prefixEnd_8115070 4166931454881669985004479 := by
  unfold tailWord_8115070
  simp only [CollatzResearch.WordTrace]
  refine ⟨36997614838811851057562833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197320612473663205640335109 36997614838811851057562833)
  ·
    refine ⟨27748211129108888293172125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36997614838811851057562833 27748211129108888293172125)
    ·
      refine ⟨10405579173415833109939547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27748211129108888293172125 10405579173415833109939547)
      ·
        refine ⟨15608368760123749664909321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10405579173415833109939547 15608368760123749664909321)
        ·
          refine ⟨11706276570092812248681991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15608368760123749664909321 11706276570092812248681991)
          ·
            refine ⟨17559414855139218373022987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11706276570092812248681991 17559414855139218373022987)
            ·
              refine ⟨26339122282708827559534481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17559414855139218373022987 26339122282708827559534481)
              ·
                refine ⟨19754341712031620669650861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26339122282708827559534481 19754341712031620669650861)
                ·
                  refine ⟨7407878142011857751119073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19754341712031620669650861 7407878142011857751119073)
                  ·
                    refine ⟨5555908606508893313339305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7407878142011857751119073 5555908606508893313339305)
                    ·
                      refine ⟨4166931454881669985004479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5555908606508893313339305 4166931454881669985004479)
                      ·
                        rfl

theorem cell23_8115070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_8115070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115070 prefixEnd_8115070 := by exact prefixLift 8115070
  have htrace : WordTrace (prefixWord ++ tailWord_8115070) baseStart_8115070 baseEnd_8115070 := by
    simpa [prefixWord, tailWord_8115070, baseEnd_8115070] using wordTrace_append hprefix tailTrace_8115070
  have hstable : (prefixWord ++ tailWord_8115070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115070).length < 2 ^ (prefixWord ++ tailWord_8115070).sum := by decide
  have hdescent : baseEnd_8115070 < baseStart_8115070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115090 : List Nat := [3, 2, 3, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_8115090 : Nat := 118140960795 + 8115090 * 2 ^ 59
def prefixEnd_8115090 : Nat := 4983230072969 + 3 ^ 40 * 8115090 * 2
def baseEnd_8115090 : Nat := 4166941724494759906754387

theorem tailTrace_8115090 : CollatzResearch.WordTrace tailWord_8115090 prefixEnd_8115090 4166941724494759906754387 := by
  unfold tailWord_8115090
  simp only [CollatzResearch.WordTrace]
  refine ⟨73995412042605587969057681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197321098780281567917487149 73995412042605587969057681)
  ·
    refine ⟨55496559031954190976793261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73995412042605587969057681 55496559031954190976793261)
    ·
      refine ⟨20811209636982821616297473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55496559031954190976793261 20811209636982821616297473)
      ·
        refine ⟨15608407227737116212223105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20811209636982821616297473 15608407227737116212223105)
        ·
          refine ⟨11706305420802837159167329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15608407227737116212223105 11706305420802837159167329)
          ·
            refine ⟨8779729065602127869375497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11706305420802837159167329 8779729065602127869375497)
            ·
              refine ⟨6584796799201595902031623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8779729065602127869375497 6584796799201595902031623)
              ·
                refine ⟨9877195198802393853047435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6584796799201595902031623 9877195198802393853047435)
                ·
                  refine ⟨14815792798203590779571153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9877195198802393853047435 14815792798203590779571153)
                  ·
                    refine ⟨11111844598652693084678365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14815792798203590779571153 11111844598652693084678365)
                    ·
                      refine ⟨4166941724494759906754387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11111844598652693084678365 4166941724494759906754387)
                      ·
                        rfl

theorem cell23_8115090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_8115090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115090 prefixEnd_8115090 := by exact prefixLift 8115090
  have htrace : WordTrace (prefixWord ++ tailWord_8115090) baseStart_8115090 baseEnd_8115090 := by
    simpa [prefixWord, tailWord_8115090, baseEnd_8115090] using wordTrace_append hprefix tailTrace_8115090
  have hstable : (prefixWord ++ tailWord_8115090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115090).length < 2 ^ (prefixWord ++ tailWord_8115090).sum := by decide
  have hdescent : baseEnd_8115090 < baseStart_8115090 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115103 : List Nat := [1, 1, 2, 5, 2, 3, 1, 2, 2, 1, 3]
def baseStart_8115103 : Nat := 118140960795 + 8115103 * 2 ^ 59
def prefixEnd_8115103 : Nat := 4983230072969 + 3 ^ 40 * 8115103 * 2
def baseEnd_8115103 : Nat := 4166948399743268355891827

theorem tailTrace_8115103 : CollatzResearch.WordTrace tailWord_8115103 prefixEnd_8115103 4166948399743268355891827 := by
  unfold tailWord_8115103
  simp only [CollatzResearch.WordTrace]
  refine ⟨295982122319375255096453963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197321414879583503397635975 295982122319375255096453963)
  ·
    refine ⟨443973183479062882644680945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295982122319375255096453963 443973183479062882644680945)
    ·
      refine ⟨332979887609297161983510709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443973183479062882644680945 332979887609297161983510709)
      ·
        refine ⟨31216864463371608935954129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 332979887609297161983510709 31216864463371608935954129)
        ·
          refine ⟨23412648347528706701965597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31216864463371608935954129 23412648347528706701965597)
          ·
            refine ⟨8779743130323265013237099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23412648347528706701965597 8779743130323265013237099)
            ·
              refine ⟨13169614695484897519855649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8779743130323265013237099 13169614695484897519855649)
              ·
                refine ⟨9877211021613673139891737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13169614695484897519855649 9877211021613673139891737)
                ·
                  refine ⟨7407908266210254854918803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9877211021613673139891737 7407908266210254854918803)
                  ·
                    refine ⟨11111862399315382282378205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7407908266210254854918803 11111862399315382282378205)
                    ·
                      refine ⟨4166948399743268355891827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11111862399315382282378205 4166948399743268355891827)
                      ·
                        rfl

theorem cell23_8115103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_8115103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115103 prefixEnd_8115103 := by exact prefixLift 8115103
  have htrace : WordTrace (prefixWord ++ tailWord_8115103) baseStart_8115103 baseEnd_8115103 := by
    simpa [prefixWord, tailWord_8115103, baseEnd_8115103] using wordTrace_append hprefix tailTrace_8115103
  have hstable : (prefixWord ++ tailWord_8115103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115103).length < 2 ^ (prefixWord ++ tailWord_8115103).sum := by decide
  have hdescent : baseEnd_8115103 < baseStart_8115103 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115115 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 11]
def baseStart_8115115 : Nat := 118140960795 + 8115115 * 2 ^ 59
def prefixEnd_8115115 : Nat := 4983230072969 + 3 ^ 40 * 8115115 * 2
def baseEnd_8115115 : Nat := 462994951279013589882419

theorem tailTrace_8115115 : CollatzResearch.WordTrace tailWord_8115115 prefixEnd_8115115 462994951279013589882419 := by
  unfold tailWord_8115115
  simp only [CollatzResearch.WordTrace]
  refine ⟨295982559995331781145890799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197321706663554520763927199 295982559995331781145890799)
  ·
    refine ⟨443973839992997671718836199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295982559995331781145890799 443973839992997671718836199)
    ·
      refine ⟨665960759989496507578254299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443973839992997671718836199 665960759989496507578254299)
      ·
        refine ⟨998941139984244761367381449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665960759989496507578254299 998941139984244761367381449)
        ·
          refine ⟨749205854988183571025536087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 998941139984244761367381449 749205854988183571025536087)
          ·
            refine ⟨1123808782482275356538304131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749205854988183571025536087 1123808782482275356538304131)
            ·
              refine ⟨1685713173723413034807456197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123808782482275356538304131 1685713173723413034807456197)
              ·
                refine ⟨316071220073139944026398037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1685713173723413034807456197 316071220073139944026398037)
                ·
                  refine ⟨462994951279013589882419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 316071220073139944026398037 462994951279013589882419)
                  ·
                    rfl

theorem cell23_8115115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 11].length) (baseStart_8115115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115115 prefixEnd_8115115 := by exact prefixLift 8115115
  have htrace : WordTrace (prefixWord ++ tailWord_8115115) baseStart_8115115 baseEnd_8115115 := by
    simpa [prefixWord, tailWord_8115115, baseEnd_8115115] using wordTrace_append hprefix tailTrace_8115115
  have hstable : (prefixWord ++ tailWord_8115115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115115).length < 2 ^ (prefixWord ++ tailWord_8115115).sum := by decide
  have hdescent : baseEnd_8115115 < baseStart_8115115 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115169 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 2, 5, 2]
def baseStart_8115169 : Nat := 118140960795 + 8115169 * 2 ^ 59
def prefixEnd_8115169 : Nat := 4983230072969 + 3 ^ 40 * 8115169 * 2
def baseEnd_8115169 : Nat := 4166982289466465097666523

theorem tailTrace_8115169 : CollatzResearch.WordTrace tailWord_8115169 prefixEnd_8115169 4166982289466465097666523 := by
  unfold tailWord_8115169
  simp only [CollatzResearch.WordTrace]
  refine ⟨295984529537136148368356561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197323019691424098912237707 295984529537136148368356561)
  ·
    refine ⟨221988397152852111276267421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295984529537136148368356561 221988397152852111276267421)
    ·
      refine ⟨83245648932319541728600283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221988397152852111276267421 83245648932319541728600283)
      ·
        refine ⟨124868473398479312592900425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83245648932319541728600283 124868473398479312592900425)
        ·
          refine ⟨93651355048859484444675319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124868473398479312592900425 93651355048859484444675319)
          ·
            refine ⟨140477032573289226667012979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93651355048859484444675319 140477032573289226667012979)
            ·
              refine ⟨210715548859933840000519469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140477032573289226667012979 210715548859933840000519469)
              ·
                refine ⟨79018330822475190000194801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210715548859933840000519469 79018330822475190000194801)
                ·
                  refine ⟨59263748116856392500146101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79018330822475190000194801 59263748116856392500146101)
                  ·
                    refine ⟨5555976385955286796888697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59263748116856392500146101 5555976385955286796888697)
                    ·
                      refine ⟨4166982289466465097666523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5555976385955286796888697 4166982289466465097666523)
                      ·
                        rfl

theorem cell23_8115169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_8115169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115169 prefixEnd_8115169 := by exact prefixLift 8115169
  have htrace : WordTrace (prefixWord ++ tailWord_8115169) baseStart_8115169 baseEnd_8115169 := by
    simpa [prefixWord, tailWord_8115169, baseEnd_8115169] using wordTrace_append hprefix tailTrace_8115169
  have hstable : (prefixWord ++ tailWord_8115169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115169).length < 2 ^ (prefixWord ++ tailWord_8115169).sum := by decide
  have hdescent : baseEnd_8115169 < baseStart_8115169 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115199 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 6, 4, 2]
def baseStart_8115199 : Nat := 118140960795 + 8115199 * 2 ^ 59
def prefixEnd_8115199 : Nat := 4983230072969 + 3 ^ 40 * 8115199 * 2
def baseEnd_8115199 : Nat := 4166997693886099980291385

theorem tailTrace_8115199 : CollatzResearch.WordTrace tailWord_8115199 prefixEnd_8115199 4166997693886099980291385 := by
  unfold tailWord_8115199
  simp only [CollatzResearch.WordTrace]
  refine ⟨295985623727027463491948651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197323749151351642327965767 295985623727027463491948651)
  ·
    refine ⟨443978435590541195237922977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295985623727027463491948651 443978435590541195237922977)
    ·
      refine ⟨332983826692905896428442233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443978435590541195237922977 332983826692905896428442233)
      ·
        refine ⟨249737870019679422321331675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332983826692905896428442233 249737870019679422321331675)
        ·
          refine ⟨374606805029519133481997513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249737870019679422321331675 374606805029519133481997513)
          ·
            refine ⟨280955103772139350111498135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374606805029519133481997513 280955103772139350111498135)
            ·
              refine ⟨421432655658209025167247203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280955103772139350111498135 421432655658209025167247203)
              ·
                refine ⟨632148983487313537750870805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421432655658209025167247203 632148983487313537750870805)
                ·
                  refine ⟨29631983600967822082072069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 632148983487313537750870805 29631983600967822082072069)
                  ·
                    refine ⟨5555996925181466640388513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29631983600967822082072069 5555996925181466640388513)
                    ·
                      refine ⟨4166997693886099980291385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5555996925181466640388513 4166997693886099980291385)
                      ·
                        rfl

theorem cell23_8115199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 4, 2].length) (baseStart_8115199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115199 prefixEnd_8115199 := by exact prefixLift 8115199
  have htrace : WordTrace (prefixWord ++ tailWord_8115199) baseStart_8115199 baseEnd_8115199 := by
    simpa [prefixWord, tailWord_8115199, baseEnd_8115199] using wordTrace_append hprefix tailTrace_8115199
  have hstable : (prefixWord ++ tailWord_8115199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115199).length < 2 ^ (prefixWord ++ tailWord_8115199).sum := by decide
  have hdescent : baseEnd_8115199 < baseStart_8115199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115276 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 4, 3, 2]
def baseStart_8115276 : Nat := 118140960795 + 8115276 * 2 ^ 59
def prefixEnd_8115276 : Nat := 4983230072969 + 3 ^ 40 * 8115276 * 2
def baseEnd_8115276 : Nat := 4167037231896496179028531

theorem tailTrace_8115276 : CollatzResearch.WordTrace tailWord_8115276 prefixEnd_8115276 4167037231896496179028531 := by
  unfold tailWord_8115276
  simp only [CollatzResearch.WordTrace]
  refine ⟨147994216073874252821250841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197325621431832337095001121 147994216073874252821250841)
  ·
    refine ⟨110995662055405689615938131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147994216073874252821250841 110995662055405689615938131)
    ·
      refine ⟨166493493083108534423907197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110995662055405689615938131 166493493083108534423907197)
      ·
        refine ⟨62435059906165700408965199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166493493083108534423907197 62435059906165700408965199)
        ·
          refine ⟨93652589859248550613447799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62435059906165700408965199 93652589859248550613447799)
          ·
            refine ⟨140478884788872825920171699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93652589859248550613447799 140478884788872825920171699)
            ·
              refine ⟨210718327183309238880257549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140478884788872825920171699 210718327183309238880257549)
              ·
                refine ⟨79019372693740964580096581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210718327183309238880257549 79019372693740964580096581)
                ·
                  refine ⟨14816132380076430858768109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79019372693740964580096581 14816132380076430858768109)
                  ·
                    refine ⟨5556049642528661572038041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14816132380076430858768109 5556049642528661572038041)
                    ·
                      refine ⟨4167037231896496179028531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5556049642528661572038041 4167037231896496179028531)
                      ·
                        rfl

theorem cell23_8115276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_8115276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115276 prefixEnd_8115276 := by exact prefixLift 8115276
  have htrace : WordTrace (prefixWord ++ tailWord_8115276) baseStart_8115276 baseEnd_8115276 := by
    simpa [prefixWord, tailWord_8115276, baseEnd_8115276] using wordTrace_append hprefix tailTrace_8115276
  have hstable : (prefixWord ++ tailWord_8115276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115276).length < 2 ^ (prefixWord ++ tailWord_8115276).sum := by decide
  have hdescent : baseEnd_8115276 < baseStart_8115276 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115289 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 3, 1, 4]
def baseStart_8115289 : Nat := 118140960795 + 8115289 * 2 ^ 59
def prefixEnd_8115289 : Nat := 4983230072969 + 3 ^ 40 * 8115289 * 2
def baseEnd_8115289 : Nat := 4167043907145004628165971

theorem tailTrace_8115289 : CollatzResearch.WordTrace tailWord_8115289 prefixEnd_8115289 4167043907145004628165971 := by
  unfold tailWord_8115289
  simp only [CollatzResearch.WordTrace]
  refine ⟨295988906296701408862724921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197325937531134272575149947 295988906296701408862724921)
  ·
    refine ⟨221991679722526056647043691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295988906296701408862724921 221991679722526056647043691)
    ·
      refine ⟨332987519583789084970565537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221991679722526056647043691 332987519583789084970565537)
      ·
        refine ⟨249740639687841813727924153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332987519583789084970565537 249740639687841813727924153)
        ·
          refine ⟨187305479765881360295943115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249740639687841813727924153 187305479765881360295943115)
          ·
            refine ⟨280958219648822040443914673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187305479765881360295943115 280958219648822040443914673)
            ·
              refine ⟨210718664736616530332936005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280958219648822040443914673 210718664736616530332936005)
              ·
                refine ⟨39509749638115599437425501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210718664736616530332936005 39509749638115599437425501)
                ·
                  refine ⟨14816156114293349789034563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39509749638115599437425501 14816156114293349789034563)
                  ·
                    refine ⟨22224234171440024683551845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14816156114293349789034563 22224234171440024683551845)
                    ·
                      refine ⟨4167043907145004628165971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22224234171440024683551845 4167043907145004628165971)
                      ·
                        rfl

theorem cell23_8115289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_8115289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115289 prefixEnd_8115289 := by exact prefixLift 8115289
  have htrace : WordTrace (prefixWord ++ tailWord_8115289) baseStart_8115289 baseEnd_8115289 := by
    simpa [prefixWord, tailWord_8115289, baseEnd_8115289] using wordTrace_append hprefix tailTrace_8115289
  have hstable : (prefixWord ++ tailWord_8115289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115289).length < 2 ^ (prefixWord ++ tailWord_8115289).sum := by decide
  have hdescent : baseEnd_8115289 < baseStart_8115289 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115319 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 4]
def baseStart_8115319 : Nat := 118140960795 + 8115319 * 2 ^ 59
def prefixEnd_8115319 : Nat := 4983230072969 + 3 ^ 40 * 8115319 * 2
def baseEnd_8115319 : Nat := 4167059311564639510790833

theorem tailTrace_8115319 : CollatzResearch.WordTrace tailWord_8115319 prefixEnd_8115319 4167059311564639510790833 := by
  unfold tailWord_8115319
  simp only [CollatzResearch.WordTrace]
  refine ⟨295990000486592723986317011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197326666991061815990878007 295990000486592723986317011)
  ·
    refine ⟨443985000729889085979475517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295990000486592723986317011 443985000729889085979475517)
    ·
      refine ⟨166494375273708407242303319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443985000729889085979475517 166494375273708407242303319)
      ·
        refine ⟨249741562910562610863454979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166494375273708407242303319 249741562910562610863454979)
        ·
          refine ⟨374612344365843916295182469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249741562910562610863454979 374612344365843916295182469)
          ·
            refine ⟨70239814568595734305346713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 374612344365843916295182469 70239814568595734305346713)
            ·
              refine ⟨52679860926446800729010035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70239814568595734305346713 52679860926446800729010035)
              ·
                refine ⟨79019791389670201093515053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52679860926446800729010035 79019791389670201093515053)
                ·
                  refine ⟨29632421771126325410068145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79019791389670201093515053 29632421771126325410068145)
                  ·
                    refine ⟨22224316328344744057551109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29632421771126325410068145 22224316328344744057551109)
                    ·
                      refine ⟨4167059311564639510790833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22224316328344744057551109 4167059311564639510790833)
                      ·
                        rfl

theorem cell23_8115319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_8115319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115319 prefixEnd_8115319 := by exact prefixLift 8115319
  have htrace : WordTrace (prefixWord ++ tailWord_8115319) baseStart_8115319 baseEnd_8115319 := by
    simpa [prefixWord, tailWord_8115319, baseEnd_8115319] using wordTrace_append hprefix tailTrace_8115319
  have hstable : (prefixWord ++ tailWord_8115319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115319).length < 2 ^ (prefixWord ++ tailWord_8115319).sum := by decide
  have hdescent : baseEnd_8115319 < baseStart_8115319 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115329 : List Nat := [1, 2, 4, 2, 2, 1, 11]
def baseStart_8115329 : Nat := 118140960795 + 8115329 * 2 ^ 59
def prefixEnd_8115329 : Nat := 4983230072969 + 3 ^ 40 * 8115329 * 2
def baseEnd_8115329 : Nat := 51445240078656598415627

theorem tailTrace_8115329 : CollatzResearch.WordTrace tailWord_8115329 prefixEnd_8115329 51445240078656598415627 := by
  unfold tailWord_8115329
  simp only [CollatzResearch.WordTrace]
  refine ⟨295990365216556495694181041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197326910144370997129454027 295990365216556495694181041)
  ·
    refine ⟨221992773912417371770635781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295990365216556495694181041 221992773912417371770635781)
    ·
      refine ⟨41623645108578257206994209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221992773912417371770635781 41623645108578257206994209)
      ·
        refine ⟨31217733831433692905245657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41623645108578257206994209 31217733831433692905245657)
        ·
          refine ⟨23413300373575269678934243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31217733831433692905245657 23413300373575269678934243)
          ·
            refine ⟨35119950560362904518401365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23413300373575269678934243 35119950560362904518401365)
            ·
              refine ⟨51445240078656598415627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 35119950560362904518401365 51445240078656598415627)
              ·
                rfl

theorem cell23_8115329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 11].length) (baseStart_8115329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115329 prefixEnd_8115329 := by exact prefixLift 8115329
  have htrace : WordTrace (prefixWord ++ tailWord_8115329) baseStart_8115329 baseEnd_8115329 := by
    simpa [prefixWord, tailWord_8115329, baseEnd_8115329] using wordTrace_append hprefix tailTrace_8115329
  have hstable : (prefixWord ++ tailWord_8115329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115329).length < 2 ^ (prefixWord ++ tailWord_8115329).sum := by decide
  have hdescent : baseEnd_8115329 < baseStart_8115329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115340 : List Nat := [2, 2, 1, 2, 1, 1, 1, 8, 1, 2, 2]
def baseStart_8115340 : Nat := 118140960795 + 8115340 * 2 ^ 59
def prefixEnd_8115340 : Nat := 4983230072969 + 3 ^ 40 * 8115340 * 2
def baseEnd_8115340 : Nat := 4167070094658383928628237

theorem tailTrace_8115340 : CollatzResearch.WordTrace tailWord_8115340 prefixEnd_8115340 4167070094658383928628237 := by
  unfold tailWord_8115340
  simp only [CollatzResearch.WordTrace]
  refine ⟨147995383209758322286415737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197327177613011096381887649 147995383209758322286415737)
  ·
    refine ⟨110996537407318741714811803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147995383209758322286415737 110996537407318741714811803)
    ·
      refine ⟨166494806110978112572217705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110996537407318741714811803 166494806110978112572217705)
      ·
        refine ⟨124871104583233584429163279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166494806110978112572217705 124871104583233584429163279)
        ·
          refine ⟨187306656874850376643744919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124871104583233584429163279 187306656874850376643744919)
          ·
            refine ⟨280959985312275564965617379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187306656874850376643744919 280959985312275564965617379)
            ·
              refine ⟨421439977968413347448426069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280959985312275564965617379 421439977968413347448426069)
              ·
                refine ⟨4938749741817343915411243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 421439977968413347448426069 4938749741817343915411243)
                ·
                  refine ⟨7408124612726015873116865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4938749741817343915411243 7408124612726015873116865)
                  ·
                    refine ⟨5556093459544511904837649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7408124612726015873116865 5556093459544511904837649)
                    ·
                      refine ⟨4167070094658383928628237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5556093459544511904837649 4167070094658383928628237)
                      ·
                        rfl

theorem cell23_8115340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 1, 2, 2].length) (baseStart_8115340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115340 prefixEnd_8115340 := by exact prefixLift 8115340
  have htrace : WordTrace (prefixWord ++ tailWord_8115340) baseStart_8115340 baseEnd_8115340 := by
    simpa [prefixWord, tailWord_8115340, baseEnd_8115340] using wordTrace_append hprefix tailTrace_8115340
  have hstable : (prefixWord ++ tailWord_8115340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115340).length < 2 ^ (prefixWord ++ tailWord_8115340).sum := by decide
  have hdescent : baseEnd_8115340 < baseStart_8115340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115346 : List Nat := [3, 2, 3, 1, 1, 3, 2, 8]
def baseStart_8115346 : Nat := 118140960795 + 8115346 * 2 ^ 59
def prefixEnd_8115346 : Nat := 4983230072969 + 3 ^ 40 * 8115346 * 2
def baseEnd_8115346 : Nat := 154336043538604107598267

theorem tailTrace_8115346 : CollatzResearch.WordTrace tailWord_8115346 prefixEnd_8115346 154336043538604107598267 := by
  unfold tailWord_8115346
  simp only [CollatzResearch.WordTrace]
  refine ⟨73997746314373726899387473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197327323504996605065033261 73997746314373726899387473)
  ·
    refine ⟨55498309735780295174540605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73997746314373726899387473 55498309735780295174540605)
    ·
      refine ⟨20811866150917610690452727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55498309735780295174540605 20811866150917610690452727)
      ·
        refine ⟨31217799226376416035679091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20811866150917610690452727 31217799226376416035679091)
        ·
          refine ⟨46826698839564624053518637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31217799226376416035679091 46826698839564624053518637)
          ·
            refine ⟨17560012064836734020069489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46826698839564624053518637 17560012064836734020069489)
            ·
              refine ⟨13170009048627550515052117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17560012064836734020069489 13170009048627550515052117)
              ·
                refine ⟨154336043538604107598267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13170009048627550515052117 154336043538604107598267)
                ·
                  rfl

theorem cell23_8115346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 8].length) (baseStart_8115346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115346 prefixEnd_8115346 := by exact prefixLift 8115346
  have htrace : WordTrace (prefixWord ++ tailWord_8115346) baseStart_8115346 baseEnd_8115346 := by
    simpa [prefixWord, tailWord_8115346, baseEnd_8115346] using wordTrace_append hprefix tailTrace_8115346
  have hstable : (prefixWord ++ tailWord_8115346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115346).length < 2 ^ (prefixWord ++ tailWord_8115346).sum := by decide
  have hdescent : baseEnd_8115346 < baseStart_8115346 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115390 : List Nat := [4, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_8115390 : Nat := 118140960795 + 8115390 * 2 ^ 59
def prefixEnd_8115390 : Nat := 4983230072969 + 3 ^ 40 * 8115390 * 2
def baseEnd_8115390 : Nat := 4167095768691108733003007

theorem tailTrace_8115390 : CollatzResearch.WordTrace tailWord_8115390 prefixEnd_8115390 4167095768691108733003007 := by
  unfold tailWord_8115390
  simp only [CollatzResearch.WordTrace]
  refine ⟨36999073758666937889018953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197328393379557002074767749 36999073758666937889018953)
  ·
    refine ⟨27749305319000203416764215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36999073758666937889018953 27749305319000203416764215)
    ·
      refine ⟨41623957978500305125146323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27749305319000203416764215 41623957978500305125146323)
      ·
        refine ⟨62435936967750457687719485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41623957978500305125146323 62435936967750457687719485)
        ·
          refine ⟨23413476362906421632894807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62435936967750457687719485 23413476362906421632894807)
          ·
            refine ⟨35120214544359632449342211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23413476362906421632894807 35120214544359632449342211)
            ·
              refine ⟨52680321816539448674013317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35120214544359632449342211 52680321816539448674013317)
              ·
                refine ⟨9877560340601146626377497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52680321816539448674013317 9877560340601146626377497)
                ·
                  refine ⟨7408170255450859969783123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9877560340601146626377497 7408170255450859969783123)
                  ·
                    refine ⟨11112255383176289954674685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7408170255450859969783123 11112255383176289954674685)
                    ·
                      refine ⟨4167095768691108733003007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11112255383176289954674685 4167095768691108733003007)
                      ·
                        rfl

theorem cell23_8115390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_8115390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115390 prefixEnd_8115390 := by exact prefixLift 8115390
  have htrace : WordTrace (prefixWord ++ tailWord_8115390) baseStart_8115390 baseEnd_8115390 := by
    simpa [prefixWord, tailWord_8115390, baseEnd_8115390] using wordTrace_append hprefix tailTrace_8115390
  have hstable : (prefixWord ++ tailWord_8115390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115390).length < 2 ^ (prefixWord ++ tailWord_8115390).sum := by decide
  have hdescent : baseEnd_8115390 < baseStart_8115390 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115399 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_8115399 : Nat := 118140960795 + 8115399 * 2 ^ 59
def prefixEnd_8115399 : Nat := 4983230072969 + 3 ^ 40 * 8115399 * 2
def baseEnd_8115399 : Nat := 4167100390016999197790465

theorem tailTrace_8115399 : CollatzResearch.WordTrace tailWord_8115399 prefixEnd_8115399 4167100390016999197790465 := by
  unfold tailWord_8115399
  simp only [CollatzResearch.WordTrace]
  refine ⟨295992918326302897649229251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197328612217535265099486167 295992918326302897649229251)
  ·
    refine ⟨443989377489454346473843877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295992918326302897649229251 443989377489454346473843877)
    ·
      refine ⟨83248008279272689963845727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 443989377489454346473843877 83248008279272689963845727)
      ·
        refine ⟨124872012418909034945768591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83248008279272689963845727 124872012418909034945768591)
        ·
          refine ⟨187308018628363552418652887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124872012418909034945768591 187308018628363552418652887)
          ·
            refine ⟨280962027942545328627979331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187308018628363552418652887 280962027942545328627979331)
            ·
              refine ⟨421443041913817992941968997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280962027942545328627979331 421443041913817992941968997)
              ·
                refine ⟨79020570358840873676619187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 421443041913817992941968997 79020570358840873676619187)
                ·
                  refine ⟨118530855538261310514928781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79020570358840873676619187 118530855538261310514928781)
                  ·
                    refine ⟨44449070826847991443098293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118530855538261310514928781 44449070826847991443098293)
                    ·
                      refine ⟨4167100390016999197790465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44449070826847991443098293 4167100390016999197790465)
                      ·
                        rfl

theorem cell23_8115399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_8115399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115399 prefixEnd_8115399 := by exact prefixLift 8115399
  have htrace : WordTrace (prefixWord ++ tailWord_8115399) baseStart_8115399 baseEnd_8115399 := by
    simpa [prefixWord, tailWord_8115399, baseEnd_8115399] using wordTrace_append hprefix tailTrace_8115399
  have hstable : (prefixWord ++ tailWord_8115399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115399).length < 2 ^ (prefixWord ++ tailWord_8115399).sum := by decide
  have hdescent : baseEnd_8115399 < baseStart_8115399 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115464 : List Nat := [2, 1, 3, 2, 4, 1, 3, 1, 2, 2, 2]
def baseStart_8115464 : Nat := 118140960795 + 8115464 * 2 ^ 59
def prefixEnd_8115464 : Nat := 4983230072969 + 3 ^ 40 * 8115464 * 2
def baseEnd_8115464 : Nat := 4167133766259541443477667

theorem tailTrace_8115464 : CollatzResearch.WordTrace tailWord_8115464 prefixEnd_8115464 4167133766259541443477667 := by
  unfold tailWord_8115464
  simp only [CollatzResearch.WordTrace]
  refine ⟨147997644535533706875172723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197330192714044942500230297 147997644535533706875172723)
  ·
    refine ⟨221996466803300560312759085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147997644535533706875172723 221996466803300560312759085)
    ·
      refine ⟨83248675051237710117284657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221996466803300560312759085 83248675051237710117284657)
      ·
        refine ⟨62436506288428282587963493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83248675051237710117284657 62436506288428282587963493)
        ·
          refine ⟨11706844929080302985243155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62436506288428282587963493 11706844929080302985243155)
          ·
            refine ⟨17560267393620454477864733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11706844929080302985243155 17560267393620454477864733)
            ·
              refine ⟨6585100272607670429199275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17560267393620454477864733 6585100272607670429199275)
              ·
                refine ⟨9877650408911505643798913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6585100272607670429199275 9877650408911505643798913)
                ·
                  refine ⟨7408237806683629232849185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9877650408911505643798913 7408237806683629232849185)
                  ·
                    refine ⟨5556178355012721924636889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7408237806683629232849185 5556178355012721924636889)
                    ·
                      refine ⟨4167133766259541443477667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5556178355012721924636889 4167133766259541443477667)
                      ·
                        rfl

theorem cell23_8115464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_8115464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115464 prefixEnd_8115464 := by exact prefixLift 8115464
  have htrace : WordTrace (prefixWord ++ tailWord_8115464) baseStart_8115464 baseEnd_8115464 := by
    simpa [prefixWord, tailWord_8115464, baseEnd_8115464] using wordTrace_append hprefix tailTrace_8115464
  have hstable : (prefixWord ++ tailWord_8115464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115464).length < 2 ^ (prefixWord ++ tailWord_8115464).sum := by decide
  have hdescent : baseEnd_8115464 < baseStart_8115464 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115487 : List Nat := [1, 1, 2, 4, 5, 1, 1, 3, 5]
def baseStart_8115487 : Nat := 118140960795 + 8115487 * 2 ^ 59
def prefixEnd_8115487 : Nat := 4983230072969 + 3 ^ 40 * 8115487 * 2
def baseEnd_8115487 : Nat := 463016175146066094832229

theorem tailTrace_8115487 : CollatzResearch.WordTrace tailWord_8115487 prefixEnd_8115487 463016175146066094832229 := by
  unfold tailWord_8115487
  simp only [CollatzResearch.WordTrace]
  refine ⟨295996127949984088678432715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197330751966656059118955143 295996127949984088678432715)
  ·
    refine ⟨443994191924976133017649073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295996127949984088678432715 443994191924976133017649073)
    ·
      refine ⟨332995643943732099763236805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443994191924976133017649073 332995643943732099763236805)
      ·
        refine ⟨62436683239449768705606901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332995643943732099763236805 62436683239449768705606901)
        ·
          refine ⟨5853439053698415816150647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62436683239449768705606901 5853439053698415816150647)
          ·
            refine ⟨8780158580547623724225971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5853439053698415816150647 8780158580547623724225971)
            ·
              refine ⟨13170237870821435586338957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8780158580547623724225971 13170237870821435586338957)
              ·
                refine ⟨4938839201558038344877109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13170237870821435586338957 4938839201558038344877109)
                ·
                  refine ⟨463016175146066094832229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4938839201558038344877109 463016175146066094832229)
                  ·
                    rfl

theorem cell23_8115487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 5].length) (baseStart_8115487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115487 prefixEnd_8115487 := by exact prefixLift 8115487
  have htrace : WordTrace (prefixWord ++ tailWord_8115487) baseStart_8115487 baseEnd_8115487 := by
    simpa [prefixWord, tailWord_8115487, baseEnd_8115487] using wordTrace_append hprefix tailTrace_8115487
  have hstable : (prefixWord ++ tailWord_8115487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115487).length < 2 ^ (prefixWord ++ tailWord_8115487).sum := by decide
  have hdescent : baseEnd_8115487 < baseStart_8115487 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115540 : List Nat := [2, 4, 1, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_8115540 : Nat := 118140960795 + 8115540 * 2 ^ 59
def prefixEnd_8115540 : Nat := 4983230072969 + 3 ^ 40 * 8115540 * 2
def baseEnd_8115540 : Nat := 4167172790789283146127317

theorem tailTrace_8115540 : CollatzResearch.WordTrace tailWord_8115540 prefixEnd_8115540 4167172790789283146127317 := by
  unfold tailWord_8115540
  simp only [CollatzResearch.WordTrace]
  refine ⟨147999030509396039365056037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197332040679194719153408049 147999030509396039365056037)
  ·
    refine ⟨27749818220511757380948007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147999030509396039365056037 27749818220511757380948007)
    ·
      refine ⟨41624727330767636071422011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27749818220511757380948007 41624727330767636071422011)
      ·
        refine ⟨62437090996151454107133017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41624727330767636071422011 62437090996151454107133017)
        ·
          refine ⟨46827818247113590580349763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62437090996151454107133017 46827818247113590580349763)
          ·
            refine ⟨70241727370670385870524645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46827818247113590580349763 70241727370670385870524645)
            ·
              refine ⟨13170323882000697350723371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70241727370670385870524645 13170323882000697350723371)
              ·
                refine ⟨19755485823001046026085057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13170323882000697350723371 19755485823001046026085057)
                ·
                  refine ⟨14816614367250784519563793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19755485823001046026085057 14816614367250784519563793)
                  ·
                    refine ⟨11112460775438088389672845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14816614367250784519563793 11112460775438088389672845)
                    ·
                      refine ⟨4167172790789283146127317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11112460775438088389672845 4167172790789283146127317)
                      ·
                        rfl

theorem cell23_8115540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_8115540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115540 prefixEnd_8115540 := by exact prefixLift 8115540
  have htrace : WordTrace (prefixWord ++ tailWord_8115540) baseStart_8115540 baseEnd_8115540 := by
    simpa [prefixWord, tailWord_8115540, baseEnd_8115540] using wordTrace_append hprefix tailTrace_8115540
  have hstable : (prefixWord ++ tailWord_8115540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115540).length < 2 ^ (prefixWord ++ tailWord_8115540).sum := by decide
  have hdescent : baseEnd_8115540 < baseStart_8115540 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115560 : List Nat := [2, 1, 4, 2, 3, 1, 2, 2, 6]
def baseStart_8115560 : Nat := 118140960795 + 8115560 * 2 ^ 59
def prefixEnd_8115560 : Nat := 4983230072969 + 3 ^ 40 * 8115560 * 2
def baseEnd_8115560 : Nat := 463020340044708118653025

theorem tailTrace_8115560 : CollatzResearch.WordTrace tailWord_8115560 prefixEnd_8115560 463020340044708118653025 := by
  unfold tailWord_8115560
  simp only [CollatzResearch.WordTrace]
  refine ⟨147999395239359811072920067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197332526985813081430560089 147999395239359811072920067)
  ·
    refine ⟨221999092859039716609380101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147999395239359811072920067 221999092859039716609380101)
    ·
      refine ⟨41624829911069946864258769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221999092859039716609380101 41624829911069946864258769)
      ·
        refine ⟨31218622433302460148194077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41624829911069946864258769 31218622433302460148194077)
        ·
          refine ⟨11706983412488422555572779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31218622433302460148194077 11706983412488422555572779)
          ·
            refine ⟨17560475118732633833359169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11706983412488422555572779 17560475118732633833359169)
            ·
              refine ⟨13170356339049475375019377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17560475118732633833359169 13170356339049475375019377)
              ·
                refine ⟨9877767254287106531264533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13170356339049475375019377 9877767254287106531264533)
                ·
                  refine ⟨463020340044708118653025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9877767254287106531264533 463020340044708118653025)
                  ·
                    rfl

theorem cell23_8115560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 6].length) (baseStart_8115560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115560 prefixEnd_8115560 := by exact prefixLift 8115560
  have htrace : WordTrace (prefixWord ++ tailWord_8115560) baseStart_8115560 baseEnd_8115560 := by
    simpa [prefixWord, tailWord_8115560, baseEnd_8115560] using wordTrace_append hprefix tailTrace_8115560
  have hstable : (prefixWord ++ tailWord_8115560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115560).length < 2 ^ (prefixWord ++ tailWord_8115560).sum := by decide
  have hdescent : baseEnd_8115560 < baseStart_8115560 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115564 : List Nat := [2, 2, 1, 1, 5, 3, 2, 2, 1, 4]
def baseStart_8115564 : Nat := 118140960795 + 8115564 * 2 ^ 59
def prefixEnd_8115564 : Nat := 4983230072969 + 3 ^ 40 * 8115564 * 2
def baseEnd_8115564 : Nat := 1389061704774997017409069

theorem tailTrace_8115564 : CollatzResearch.WordTrace tailWord_8115564 prefixEnd_8115564 1389061704774997017409069 := by
  unfold tailWord_8115564
  simp only [CollatzResearch.WordTrace]
  refine ⟨147999468185352565414492873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197332624247136753885990497 147999468185352565414492873)
  ·
    refine ⟨110999601139014424060869655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147999468185352565414492873 110999601139014424060869655)
    ·
      refine ⟨166499401708521636091304483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110999601139014424060869655 166499401708521636091304483)
      ·
        refine ⟨249749102562782454136956725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166499401708521636091304483 249749102562782454136956725)
        ·
          refine ⟨23413978365260855075339693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249749102562782454136956725 23413978365260855075339693)
          ·
            refine ⟨8780241886972820653252385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23413978365260855075339693 8780241886972820653252385)
            ·
              refine ⟨6585181415229615489939289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8780241886972820653252385 6585181415229615489939289)
              ·
                refine ⟨4938886061422211617454467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6585181415229615489939289 4938886061422211617454467)
                ·
                  refine ⟨7408329092133317426181701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4938886061422211617454467 7408329092133317426181701)
                  ·
                    refine ⟨1389061704774997017409069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7408329092133317426181701 1389061704774997017409069)
                    ·
                      rfl

theorem cell23_8115564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 1, 4].length) (baseStart_8115564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115564 prefixEnd_8115564 := by exact prefixLift 8115564
  have htrace : WordTrace (prefixWord ++ tailWord_8115564) baseStart_8115564 baseEnd_8115564 := by
    simpa [prefixWord, tailWord_8115564, baseEnd_8115564] using wordTrace_append hprefix tailTrace_8115564
  have hstable : (prefixWord ++ tailWord_8115564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115564).length < 2 ^ (prefixWord ++ tailWord_8115564).sum := by decide
  have hdescent : baseEnd_8115564 < baseStart_8115564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115570 : List Nat := [3, 2, 1, 2, 1, 2, 2, 3, 3, 1, 3]
def baseStart_8115570 : Nat := 118140960795 + 8115570 * 2 ^ 59
def prefixEnd_8115570 : Nat := 4983230072969 + 3 ^ 40 * 8115570 * 2
def baseEnd_8115570 : Nat := 4167188195208918028752179

theorem tailTrace_8115570 : CollatzResearch.WordTrace tailWord_8115570 prefixEnd_8115570 4167188195208918028752179 := by
  unfold tailWord_8115570
  simp only [CollatzResearch.WordTrace]
  refine ⟨73999788802170848463426041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197332770139122262569136109 73999788802170848463426041)
  ·
    refine ⟨55499841601628136347569531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73999788802170848463426041 55499841601628136347569531)
    ·
      refine ⟨83249762402442204521354297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55499841601628136347569531 83249762402442204521354297)
      ·
        refine ⟨62437321801831653391015723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83249762402442204521354297 62437321801831653391015723)
        ·
          refine ⟨93655982702747480086523585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62437321801831653391015723 93655982702747480086523585)
          ·
            refine ⟨70241987027060610064892689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93655982702747480086523585 70241987027060610064892689)
            ·
              refine ⟨52681490270295457548669517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70241987027060610064892689 52681490270295457548669517)
              ·
                refine ⟨19755558851360796580751069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52681490270295457548669517 19755558851360796580751069)
                ·
                  refine ⟨7408334569260298717781651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19755558851360796580751069 7408334569260298717781651)
                  ·
                    refine ⟨11112501853890448076672477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7408334569260298717781651 11112501853890448076672477)
                    ·
                      refine ⟨4167188195208918028752179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11112501853890448076672477 4167188195208918028752179)
                      ·
                        rfl

theorem cell23_8115570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_8115570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115570 prefixEnd_8115570 := by exact prefixLift 8115570
  have htrace : WordTrace (prefixWord ++ tailWord_8115570) baseStart_8115570 baseEnd_8115570 := by
    simpa [prefixWord, tailWord_8115570, baseEnd_8115570] using wordTrace_append hprefix tailTrace_8115570
  have hstable : (prefixWord ++ tailWord_8115570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115570).length < 2 ^ (prefixWord ++ tailWord_8115570).sum := by decide
  have hdescent : baseEnd_8115570 < baseStart_8115570 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115604 : List Nat := [2, 4, 2, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_8115604 : Nat := 118140960795 + 8115604 * 2 ^ 59
def prefixEnd_8115604 : Nat := 4983230072969 + 3 ^ 40 * 8115604 * 2
def baseEnd_8115604 : Nat := 4167205653551170895727023

theorem tailTrace_8115604 : CollatzResearch.WordTrace tailWord_8115604 prefixEnd_8115604 4167205653551170895727023 := by
  unfold tailWord_8115604
  simp only [CollatzResearch.WordTrace]
  refine ⟨148000197645280108830220933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197333596860373478440294577 148000197645280108830220933)
  ·
    refine ⟨27750037058490020405666425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148000197645280108830220933 27750037058490020405666425)
    ·
      refine ⟨20812527793867515304249819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27750037058490020405666425 20812527793867515304249819)
      ·
        refine ⟨31218791690801272956374729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20812527793867515304249819 31218791690801272956374729)
        ·
          refine ⟨23414093768100954717281047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31218791690801272956374729 23414093768100954717281047)
          ·
            refine ⟨35121140652151432075921571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23414093768100954717281047 35121140652151432075921571)
            ·
              refine ⟨52681710978227148113882357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35121140652151432075921571 52681710978227148113882357)
              ·
                refine ⟨4938910404208795135676471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52681710978227148113882357 4938910404208795135676471)
                ·
                  refine ⟨7408365606313192703514707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4938910404208795135676471 7408365606313192703514707)
                  ·
                    refine ⟨11112548409469789055272061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7408365606313192703514707 11112548409469789055272061)
                    ·
                      refine ⟨4167205653551170895727023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11112548409469789055272061 4167205653551170895727023)
                      ·
                        rfl

theorem cell23_8115604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_8115604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115604 prefixEnd_8115604 := by exact prefixLift 8115604
  have htrace : WordTrace (prefixWord ++ tailWord_8115604) baseStart_8115604 baseEnd_8115604 := by
    simpa [prefixWord, tailWord_8115604, baseEnd_8115604] using wordTrace_append hprefix tailTrace_8115604
  have hstable : (prefixWord ++ tailWord_8115604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115604).length < 2 ^ (prefixWord ++ tailWord_8115604).sum := by decide
  have hdescent : baseEnd_8115604 < baseStart_8115604 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115610 : List Nat := [3, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4]
def baseStart_8115610 : Nat := 118140960795 + 8115610 * 2 ^ 59
def prefixEnd_8115610 : Nat := 4983230072969 + 3 ^ 40 * 8115610 * 2
def baseEnd_8115610 : Nat := 4167208734435097872251995

theorem tailTrace_8115610 : CollatzResearch.WordTrace tailWord_8115610 prefixEnd_8115610 4167208734435097872251995 := by
  unfold tailWord_8115610
  simp only [CollatzResearch.WordTrace]
  refine ⟨74000153532134620171290071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197333742752358987123440189 74000153532134620171290071)
  ·
    refine ⟨111000230298201930256935107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74000153532134620171290071 111000230298201930256935107)
    ·
      refine ⟨166500345447302895385402661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111000230298201930256935107 166500345447302895385402661)
      ·
        refine ⟨31218814771369292884762999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166500345447302895385402661 31218814771369292884762999)
        ·
          refine ⟨46828222157053939327144499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31218814771369292884762999 46828222157053939327144499)
          ·
            refine ⟨70242333235580908990716749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46828222157053939327144499 70242333235580908990716749)
            ·
              refine ⟨26340874963342840871518781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70242333235580908990716749 26340874963342840871518781)
              ·
                refine ⟨9877828111253565326819543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26340874963342840871518781 9877828111253565326819543)
                ·
                  refine ⟨14816742166880347990229315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9877828111253565326819543 14816742166880347990229315)
                  ·
                    refine ⟨22225113250320521985343973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14816742166880347990229315 22225113250320521985343973)
                    ·
                      refine ⟨4167208734435097872251995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22225113250320521985343973 4167208734435097872251995)
                      ·
                        rfl

theorem cell23_8115610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_8115610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115610 prefixEnd_8115610 := by exact prefixLift 8115610
  have htrace : WordTrace (prefixWord ++ tailWord_8115610) baseStart_8115610 baseEnd_8115610 := by
    simpa [prefixWord, tailWord_8115610, baseEnd_8115610] using wordTrace_append hprefix tailTrace_8115610
  have hstable : (prefixWord ++ tailWord_8115610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115610).length < 2 ^ (prefixWord ++ tailWord_8115610).sum := by decide
  have hdescent : baseEnd_8115610 < baseStart_8115610 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115616 : List Nat := [2, 1, 1, 4, 1, 2, 12]
def baseStart_8115616 : Nat := 118140960795 + 8115616 * 2 ^ 59
def prefixEnd_8115616 : Nat := 4983230072969 + 3 ^ 40 * 8115616 * 2
def baseEnd_8115616 : Nat := 51447059448383022824407

theorem tailTrace_8115616 : CollatzResearch.WordTrace tailWord_8115616 prefixEnd_8115616 51447059448383022824407 := by
  unfold tailWord_8115616
  simp only [CollatzResearch.WordTrace]
  refine ⟨148000416483258371854939351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197333888644344495806585801 148000416483258371854939351)
  ·
    refine ⟨222000624724887557782409027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148000416483258371854939351 222000624724887557782409027)
    ·
      refine ⟨333000937087331336673613541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222000624724887557782409027 333000937087331336673613541)
      ·
        refine ⟨62437675703874625626302539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333000937087331336673613541 62437675703874625626302539)
        ·
          refine ⟨93656513555811938439453809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62437675703874625626302539 93656513555811938439453809)
          ·
            refine ⟨70242385166858953829590357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93656513555811938439453809 70242385166858953829590357)
            ·
              refine ⟨51447059448383022824407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 70242385166858953829590357 51447059448383022824407)
              ·
                rfl

theorem cell23_8115616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 12].length) (baseStart_8115616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115616 prefixEnd_8115616 := by exact prefixLift 8115616
  have htrace : WordTrace (prefixWord ++ tailWord_8115616) baseStart_8115616 baseEnd_8115616 := by
    simpa [prefixWord, tailWord_8115616, baseEnd_8115616] using wordTrace_append hprefix tailTrace_8115616
  have hstable : (prefixWord ++ tailWord_8115616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115616).length < 2 ^ (prefixWord ++ tailWord_8115616).sum := by decide
  have hdescent : baseEnd_8115616 < baseStart_8115616 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115623 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_8115623 : Nat := 118140960795 + 8115623 * 2 ^ 59
def prefixEnd_8115623 : Nat := 4983230072969 + 3 ^ 40 * 8115623 * 2
def baseEnd_8115623 : Nat := 4167215409683606321389435

theorem tailTrace_8115623 : CollatzResearch.WordTrace tailWord_8115623 prefixEnd_8115623 4167215409683606321389435 := by
  unfold tailWord_8115623
  simp only [CollatzResearch.WordTrace]
  refine ⟨296001088277491383905383523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197334058851660922603589015 296001088277491383905383523)
  ·
    refine ⟨444001632416237075858075285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296001088277491383905383523 444001632416237075858075285)
    ·
      refine ⟨20812576519511112930847279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 444001632416237075858075285 20812576519511112930847279)
      ·
        refine ⟨31218864779266669396270919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20812576519511112930847279 31218864779266669396270919)
        ·
          refine ⟨46828297168900004094406379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31218864779266669396270919 46828297168900004094406379)
          ·
            refine ⟨70242445753350006141609569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46828297168900004094406379 70242445753350006141609569)
            ·
              refine ⟨52681834315012504606207177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70242445753350006141609569 52681834315012504606207177)
              ·
                refine ⟨39511375736259378454655383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52681834315012504606207177 39511375736259378454655383)
                ·
                  refine ⟨59267063604389067681983075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39511375736259378454655383 59267063604389067681983075)
                  ·
                    refine ⟨88900595406583601522974613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59267063604389067681983075 88900595406583601522974613)
                    ·
                      refine ⟨4167215409683606321389435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88900595406583601522974613 4167215409683606321389435)
                      ·
                        rfl

theorem cell23_8115623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_8115623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115623 prefixEnd_8115623 := by exact prefixLift 8115623
  have htrace : WordTrace (prefixWord ++ tailWord_8115623) baseStart_8115623 baseEnd_8115623 := by
    simpa [prefixWord, tailWord_8115623, baseEnd_8115623] using wordTrace_append hprefix tailTrace_8115623
  have hstable : (prefixWord ++ tailWord_8115623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115623).length < 2 ^ (prefixWord ++ tailWord_8115623).sum := by decide
  have hdescent : baseEnd_8115623 < baseStart_8115623 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115677 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_8115677 : Nat := 118140960795 + 8115677 * 2 ^ 59
def prefixEnd_8115677 : Nat := 4983230072969 + 3 ^ 40 * 8115677 * 2
def baseEnd_8115677 : Nat := 4167243137638949110114187

theorem tailTrace_8115677 : CollatzResearch.WordTrace tailWord_8115677 prefixEnd_8115677 4167243137638949110114187 := by
  unfold tailWord_8115677
  simp only [CollatzResearch.WordTrace]
  refine ⟨296003057819295751127849285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197335371879530500751899523 296003057819295751127849285)
  ·
    refine ⟨55500573341117953336471741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296003057819295751127849285 55500573341117953336471741)
    ·
      refine ⟨20812715002919232501176903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55500573341117953336471741 20812715002919232501176903)
      ·
        refine ⟨31219072504378848751765355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20812715002919232501176903 31219072504378848751765355)
        ·
          refine ⟨46828608756568273127648033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31219072504378848751765355 46828608756568273127648033)
          ·
            refine ⟨35121456567426204845736025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46828608756568273127648033 35121456567426204845736025)
            ·
              refine ⟨26341092425569653634302019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35121456567426204845736025 26341092425569653634302019)
              ·
                refine ⟨39511638638354480451453029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26341092425569653634302019 39511638638354480451453029)
                ·
                  refine ⟨7408432244691465084647443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39511638638354480451453029 7408432244691465084647443)
                  ·
                    refine ⟨11112648367037197626971165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7408432244691465084647443 11112648367037197626971165)
                    ·
                      refine ⟨4167243137638949110114187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11112648367037197626971165 4167243137638949110114187)
                      ·
                        rfl

theorem cell23_8115677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_8115677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115677 prefixEnd_8115677 := by exact prefixLift 8115677
  have htrace : WordTrace (prefixWord ++ tailWord_8115677) baseStart_8115677 baseEnd_8115677 := by
    simpa [prefixWord, tailWord_8115677, baseEnd_8115677] using wordTrace_append hprefix tailTrace_8115677
  have hstable : (prefixWord ++ tailWord_8115677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115677).length < 2 ^ (prefixWord ++ tailWord_8115677).sum := by decide
  have hdescent : baseEnd_8115677 < baseStart_8115677 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115703 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 3]
def baseStart_8115703 : Nat := 118140960795 + 8115703 * 2 ^ 59
def prefixEnd_8115703 : Nat := 4983230072969 + 3 ^ 40 * 8115703 * 2
def baseEnd_8115703 : Nat := 4167256488135966008389067

theorem tailTrace_8115703 : CollatzResearch.WordTrace tailWord_8115703 prefixEnd_8115703 4167256488135966008389067 := by
  unfold tailWord_8115703
  simp only [CollatzResearch.WordTrace]
  refine ⟨296004006117201557568295763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197336004078134371712197175 296004006117201557568295763)
  ·
    refine ⟨444006009175802336352443645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296004006117201557568295763 444006009175802336352443645)
    ·
      refine ⟨166502253440925876132166367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444006009175802336352443645 166502253440925876132166367)
      ·
        refine ⟨249753380161388814198249551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166502253440925876132166367 249753380161388814198249551)
        ·
          refine ⟨374630070242083221297374327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249753380161388814198249551 374630070242083221297374327)
          ·
            refine ⟨561945105363124831946061491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374630070242083221297374327 561945105363124831946061491)
            ·
              refine ⟨842917658044687247919092237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561945105363124831946061491 842917658044687247919092237)
              ·
                refine ⟨316094121766757717969659589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 842917658044687247919092237 316094121766757717969659589)
                ·
                  refine ⟨59267647831267072119311173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316094121766757717969659589 59267647831267072119311173)
                  ·
                    refine ⟨11112683968362576022370845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59267647831267072119311173 11112683968362576022370845)
                    ·
                      refine ⟨4167256488135966008389067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11112683968362576022370845 4167256488135966008389067)
                      ·
                        rfl

theorem cell23_8115703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_8115703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115703 prefixEnd_8115703 := by exact prefixLift 8115703
  have htrace : WordTrace (prefixWord ++ tailWord_8115703) baseStart_8115703 baseEnd_8115703 := by
    simpa [prefixWord, tailWord_8115703, baseEnd_8115703] using wordTrace_append hprefix tailTrace_8115703
  have hstable : (prefixWord ++ tailWord_8115703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115703).length < 2 ^ (prefixWord ++ tailWord_8115703).sum := by decide
  have hdescent : baseEnd_8115703 < baseStart_8115703 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115704 : List Nat := [2, 1, 2, 1, 1, 7, 1, 2, 1, 3, 2]
def baseStart_8115704 : Nat := 118140960795 + 8115704 * 2 ^ 59
def prefixEnd_8115704 : Nat := 4983230072969 + 3 ^ 40 * 8115704 * 2
def baseEnd_8115704 : Nat := 4167257001616620504476563

theorem tailTrace_8115704 : CollatzResearch.WordTrace tailWord_8115704 prefixEnd_8115704 4167257001616620504476563 := by
  unfold tailWord_8115704
  simp only [CollatzResearch.WordTrace]
  refine ⟨148002021295098967369541083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197336028393465289826054777 148002021295098967369541083)
  ·
    refine ⟨222003031942648451054311625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148002021295098967369541083 222003031942648451054311625)
    ·
      refine ⟨166502273956986338290733719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222003031942648451054311625 166502273956986338290733719)
      ·
        refine ⟨249753410935479507436100579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166502273956986338290733719 249753410935479507436100579)
        ·
          refine ⟨374630116403219261154150869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249753410935479507436100579 374630116403219261154150869)
          ·
            refine ⟨8780393353200451433300411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 374630116403219261154150869 8780393353200451433300411)
            ·
              refine ⟨13170590029800677149950617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8780393353200451433300411 13170590029800677149950617)
              ·
                refine ⟨9877942522350507862462963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13170590029800677149950617 9877942522350507862462963)
                ·
                  refine ⟨14816913783525761793694445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9877942522350507862462963 14816913783525761793694445)
                  ·
                    refine ⟨5556342668822160672635417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14816913783525761793694445 5556342668822160672635417)
                    ·
                      refine ⟨4167257001616620504476563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5556342668822160672635417 4167257001616620504476563)
                      ·
                        rfl

theorem cell23_8115704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 1, 3, 2].length) (baseStart_8115704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115704 prefixEnd_8115704 := by exact prefixLift 8115704
  have htrace : WordTrace (prefixWord ++ tailWord_8115704) baseStart_8115704 baseEnd_8115704 := by
    simpa [prefixWord, tailWord_8115704, baseEnd_8115704] using wordTrace_append hprefix tailTrace_8115704
  have hstable : (prefixWord ++ tailWord_8115704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115704).length < 2 ^ (prefixWord ++ tailWord_8115704).sum := by decide
  have hdescent : baseEnd_8115704 < baseStart_8115704 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115760 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 4, 5, 2]
def baseStart_8115760 : Nat := 118140960795 + 8115760 * 2 ^ 59
def prefixEnd_8115760 : Nat := 4983230072969 + 3 ^ 40 * 8115760 * 2
def baseEnd_8115760 : Nat := 4167285756533272285376305

theorem tailTrace_8115760 : CollatzResearch.WordTrace tailWord_8115760 prefixEnd_8115760 4167285756533272285376305 := by
  unfold tailWord_8115760
  simp only [CollatzResearch.WordTrace]
  refine ⟨148003042538997528151560367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197337390051996704202080489 148003042538997528151560367)
  ·
    refine ⟨222004563808496292227340551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148003042538997528151560367 222004563808496292227340551)
    ·
      refine ⟨333006845712744438341010827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222004563808496292227340551 333006845712744438341010827)
      ·
        refine ⟨499510268569116657511516241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333006845712744438341010827 499510268569116657511516241)
        ·
          refine ⟨374632701426837493133637181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499510268569116657511516241 374632701426837493133637181)
          ·
            refine ⟨140487263035064059925113943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374632701426837493133637181 140487263035064059925113943)
            ·
              refine ⟨210730894552596089887670915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140487263035064059925113943 210730894552596089887670915)
              ·
                refine ⟨316096341828894134831506373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210730894552596089887670915 316096341828894134831506373)
                ·
                  refine ⟨59268064092917650280907445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316096341828894134831506373 59268064092917650280907445)
                  ·
                    refine ⟨5556381008711029713835073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59268064092917650280907445 5556381008711029713835073)
                    ·
                      refine ⟨4167285756533272285376305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5556381008711029713835073 4167285756533272285376305)
                      ·
                        rfl

theorem cell23_8115760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 4, 5, 2].length) (baseStart_8115760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115760 prefixEnd_8115760 := by exact prefixLift 8115760
  have htrace : WordTrace (prefixWord ++ tailWord_8115760) baseStart_8115760 baseEnd_8115760 := by
    simpa [prefixWord, tailWord_8115760, baseEnd_8115760] using wordTrace_append hprefix tailTrace_8115760
  have hstable : (prefixWord ++ tailWord_8115760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115760).length < 2 ^ (prefixWord ++ tailWord_8115760).sum := by decide
  have hdescent : baseEnd_8115760 < baseStart_8115760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115790 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_8115790 : Nat := 118140960795 + 8115790 * 2 ^ 59
def prefixEnd_8115790 : Nat := 4983230072969 + 3 ^ 40 * 8115790 * 2
def baseEnd_8115790 : Nat := 4167301160952907168001167

theorem tailTrace_8115790 : CollatzResearch.WordTrace tailWord_8115790 prefixEnd_8115790 4167301160952907168001167 := by
  unfold tailWord_8115790
  simp only [CollatzResearch.WordTrace]
  refine ⟨37000897408485796428339103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197338119511924247617808549 37000897408485796428339103)
  ·
    refine ⟨55501346112728694642508655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37000897408485796428339103 55501346112728694642508655)
    ·
      refine ⟨83252019169093041963762983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55501346112728694642508655 83252019169093041963762983)
      ·
        refine ⟨124878028753639562945644475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83252019169093041963762983 124878028753639562945644475)
        ·
          refine ⟨187317043130459344418466713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124878028753639562945644475 187317043130459344418466713)
          ·
            refine ⟨140487782347844508313850035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187317043130459344418466713 140487782347844508313850035)
            ·
              refine ⟨210731673521766762470775053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140487782347844508313850035 210731673521766762470775053)
              ·
                refine ⟨79024377570662535926540645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210731673521766762470775053 79024377570662535926540645)
                ·
                  refine ⟨14817070794499225486226371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79024377570662535926540645 14817070794499225486226371)
                  ·
                    refine ⟨22225606191748838229339557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14817070794499225486226371 22225606191748838229339557)
                    ·
                      refine ⟨4167301160952907168001167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22225606191748838229339557 4167301160952907168001167)
                      ·
                        rfl

theorem cell23_8115790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_8115790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115790 prefixEnd_8115790 := by exact prefixLift 8115790
  have htrace : WordTrace (prefixWord ++ tailWord_8115790) baseStart_8115790 baseEnd_8115790 := by
    simpa [prefixWord, tailWord_8115790, baseEnd_8115790] using wordTrace_append hprefix tailTrace_8115790
  have hstable : (prefixWord ++ tailWord_8115790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115790).length < 2 ^ (prefixWord ++ tailWord_8115790).sum := by decide
  have hdescent : baseEnd_8115790 < baseStart_8115790 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115844 : List Nat := [2, 3, 2, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_8115844 : Nat := 118140960795 + 8115844 * 2 ^ 59
def prefixEnd_8115844 : Nat := 4983230072969 + 3 ^ 40 * 8115844 * 2
def baseEnd_8115844 : Nat := 4167328888908249956725919

theorem tailTrace_8115844 : CollatzResearch.WordTrace tailWord_8115844 prefixEnd_8115844 4167328888908249956725919 := by
  unfold tailWord_8115844
  simp only [CollatzResearch.WordTrace]
  refine ⟨148004574404845369324589293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197339432539793825766119057 148004574404845369324589293)
  ·
    refine ⟨55501715401817013496720985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148004574404845369324589293 55501715401817013496720985)
    ·
      refine ⟨41626286551362760122540739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55501715401817013496720985 41626286551362760122540739)
      ·
        refine ⟨62439429827044140183811109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41626286551362760122540739 62439429827044140183811109)
        ·
          refine ⟨11707393092570776284464583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62439429827044140183811109 11707393092570776284464583)
          ·
            refine ⟨17561089638856164426696875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11707393092570776284464583 17561089638856164426696875)
            ·
              refine ⟨26341634458284246640045313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17561089638856164426696875 26341634458284246640045313)
              ·
                refine ⟨19756225843713184980033985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26341634458284246640045313 19756225843713184980033985)
                ·
                  refine ⟨14817169382784888735025489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19756225843713184980033985 14817169382784888735025489)
                  ·
                    refine ⟨11112877037088666551269117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14817169382784888735025489 11112877037088666551269117)
                    ·
                      refine ⟨4167328888908249956725919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11112877037088666551269117 4167328888908249956725919)
                      ·
                        rfl

theorem cell23_8115844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_8115844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115844 prefixEnd_8115844 := by exact prefixLift 8115844
  have htrace : WordTrace (prefixWord ++ tailWord_8115844) baseStart_8115844 baseEnd_8115844 := by
    simpa [prefixWord, tailWord_8115844, baseEnd_8115844] using wordTrace_append hprefix tailTrace_8115844
  have hstable : (prefixWord ++ tailWord_8115844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115844).length < 2 ^ (prefixWord ++ tailWord_8115844).sum := by decide
  have hdescent : baseEnd_8115844 < baseStart_8115844 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115857 : List Nat := [1, 2, 2, 1, 1, 1, 1, 7, 3, 1, 3]
def baseStart_8115857 : Nat := 118140960795 + 8115857 * 2 ^ 59
def prefixEnd_8115857 : Nat := 4983230072969 + 3 ^ 40 * 8115857 * 2
def baseEnd_8115857 : Nat := 4167335564156758405863359

theorem tailTrace_8115857 : CollatzResearch.WordTrace tailWord_8115857 prefixEnd_8115857 4167335564156758405863359 := by
  unfold tailWord_8115857
  simp only [CollatzResearch.WordTrace]
  refine ⟨296009622958643641869401825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197339748639095761246267883 296009622958643641869401825)
  ·
    refine ⟨222007217218982731402051369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296009622958643641869401825 222007217218982731402051369)
    ·
      refine ⟨166505412914237048551538527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222007217218982731402051369 166505412914237048551538527)
      ·
        refine ⟨249758119371355572827307791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166505412914237048551538527 249758119371355572827307791)
        ·
          refine ⟨374637179057033359240961687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249758119371355572827307791 374637179057033359240961687)
          ·
            refine ⟨561955768585550038861442531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374637179057033359240961687 561955768585550038861442531)
            ·
              refine ⟨842933652878325058292163797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561955768585550038861442531 842933652878325058292163797)
              ·
                refine ⟨19756257489335743553722589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 842933652878325058292163797 19756257489335743553722589)
                ·
                  refine ⟨7408596558500903832645971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19756257489335743553722589 7408596558500903832645971)
                  ·
                    refine ⟨11112894837751355748968957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7408596558500903832645971 11112894837751355748968957)
                    ·
                      refine ⟨4167335564156758405863359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11112894837751355748968957 4167335564156758405863359)
                      ·
                        rfl

theorem cell23_8115857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 1, 3].length) (baseStart_8115857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115857 prefixEnd_8115857 := by exact prefixLift 8115857
  have htrace : WordTrace (prefixWord ++ tailWord_8115857) baseStart_8115857 baseEnd_8115857 := by
    simpa [prefixWord, tailWord_8115857, baseEnd_8115857] using wordTrace_append hprefix tailTrace_8115857
  have hstable : (prefixWord ++ tailWord_8115857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115857).length < 2 ^ (prefixWord ++ tailWord_8115857).sum := by decide
  have hdescent : baseEnd_8115857 < baseStart_8115857 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115864 : List Nat := [2, 1, 2, 4, 1, 4, 2, 1, 6]
def baseStart_8115864 : Nat := 118140960795 + 8115864 * 2 ^ 59
def prefixEnd_8115864 : Nat := 4983230072969 + 3 ^ 40 * 8115864 * 2
def baseEnd_8115864 : Nat := 463037684280148875386203

theorem tailTrace_8115864 : CollatzResearch.WordTrace tailWord_8115864 prefixEnd_8115864 463037684280148875386203 := by
  unfold tailWord_8115864
  simp only [CollatzResearch.WordTrace]
  refine ⟨148004939134809141032453323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197339918846412188043271097 148004939134809141032453323)
  ·
    refine ⟨222007408702213711548679985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148004939134809141032453323 222007408702213711548679985)
    ·
      refine ⟨166505556526660283661509989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222007408702213711548679985 166505556526660283661509989)
      ·
        refine ⟨31219791848748803186533123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166505556526660283661509989 31219791848748803186533123)
        ·
          refine ⟨46829687773123204779799685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31219791848748803186533123 46829687773123204779799685)
          ·
            refine ⟨8780566457460600896212441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46829687773123204779799685 8780566457460600896212441)
            ·
              refine ⟨6585424843095450672159331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8780566457460600896212441 6585424843095450672159331)
              ·
                refine ⟨9878137264643176008238997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6585424843095450672159331 9878137264643176008238997)
                ·
                  refine ⟨463037684280148875386203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9878137264643176008238997 463037684280148875386203)
                  ·
                    rfl

theorem cell23_8115864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 6].length) (baseStart_8115864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115864 prefixEnd_8115864 := by exact prefixLift 8115864
  have htrace : WordTrace (prefixWord ++ tailWord_8115864) baseStart_8115864 baseEnd_8115864 := by
    simpa [prefixWord, tailWord_8115864, baseEnd_8115864] using wordTrace_append hprefix tailTrace_8115864
  have hstable : (prefixWord ++ tailWord_8115864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115864).length < 2 ^ (prefixWord ++ tailWord_8115864).sum := by decide
  have hdescent : baseEnd_8115864 < baseStart_8115864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115877 : List Nat := [1, 3, 1, 2, 1, 2, 5, 2, 1, 5]
def baseStart_8115877 : Nat := 118140960795 + 8115877 * 2 ^ 59
def prefixEnd_8115877 : Nat := 4983230072969 + 3 ^ 40 * 8115877 * 2
def baseEnd_8115877 : Nat := 1389115277923282775871089

theorem tailTrace_8115877 : CollatzResearch.WordTrace tailWord_8115877 prefixEnd_8115877 1389115277923282775871089 := by
  unfold tailWord_8115877
  simp only [CollatzResearch.WordTrace]
  refine ⟨296010352418571185285129885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197340234945714123523419923 296010352418571185285129885)
  ·
    refine ⟨111003882156964194481923707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296010352418571185285129885 111003882156964194481923707)
    ·
      refine ⟨166505823235446291722885561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111003882156964194481923707 166505823235446291722885561)
      ·
        refine ⟨124879367426584718792164171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166505823235446291722885561 124879367426584718792164171)
        ·
          refine ⟨187319051139877078188246257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124879367426584718792164171 187319051139877078188246257)
          ·
            refine ⟨140489288354907808641184693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187319051139877078188246257 140489288354907808641184693)
            ·
              refine ⟨13170870783272607060111065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140489288354907808641184693 13170870783272607060111065)
              ·
                refine ⟨9878153087454455295083299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13170870783272607060111065 9878153087454455295083299)
                ·
                  refine ⟨14817229631181682942624949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9878153087454455295083299 14817229631181682942624949)
                  ·
                    refine ⟨1389115277923282775871089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14817229631181682942624949 1389115277923282775871089)
                    ·
                      rfl

theorem cell23_8115877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_8115877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115877 prefixEnd_8115877 := by exact prefixLift 8115877
  have htrace : WordTrace (prefixWord ++ tailWord_8115877) baseStart_8115877 baseEnd_8115877 := by
    simpa [prefixWord, tailWord_8115877, baseEnd_8115877] using wordTrace_append hprefix tailTrace_8115877
  have hstable : (prefixWord ++ tailWord_8115877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115877).length < 2 ^ (prefixWord ++ tailWord_8115877).sum := by decide
  have hdescent : baseEnd_8115877 < baseStart_8115877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115890 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 3, 6]
def baseStart_8115890 : Nat := 118140960795 + 8115890 * 2 ^ 59
def prefixEnd_8115890 : Nat := 4983230072969 + 3 ^ 40 * 8115890 * 2
def baseEnd_8115890 : Nat := 1389117503006118925583569

theorem tailTrace_8115890 : CollatzResearch.WordTrace tailWord_8115890 prefixEnd_8115890 1389117503006118925583569 := by
  unfold tailWord_8115890
  simp only [CollatzResearch.WordTrace]
  refine ⟨74002706641881022126338281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197340551045016059003568749 74002706641881022126338281)
  ·
    refine ⟨55502029981410766594753711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74002706641881022126338281 55502029981410766594753711)
    ·
      refine ⟨83253044972116149892130567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55502029981410766594753711 83253044972116149892130567)
      ·
        refine ⟨124879567458174224838195851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83253044972116149892130567 124879567458174224838195851)
        ·
          refine ⟨187319351187261337257293777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124879567458174224838195851 187319351187261337257293777)
          ·
            refine ⟨140489513390446002942970333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187319351187261337257293777 140489513390446002942970333)
            ·
              refine ⟨52683567521417251103613875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140489513390446002942970333 52683567521417251103613875)
              ·
                refine ⟨79025351282125876655420813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52683567521417251103613875 79025351282125876655420813)
                ·
                  refine ⟨29634506730797203745782805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79025351282125876655420813 29634506730797203745782805)
                  ·
                    refine ⟨1389117503006118925583569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29634506730797203745782805 1389117503006118925583569)
                    ·
                      rfl

theorem cell23_8115890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_8115890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115890 prefixEnd_8115890 := by exact prefixLift 8115890
  have htrace : WordTrace (prefixWord ++ tailWord_8115890) baseStart_8115890 baseEnd_8115890 := by
    simpa [prefixWord, tailWord_8115890, baseEnd_8115890] using wordTrace_append hprefix tailTrace_8115890
  have hstable : (prefixWord ++ tailWord_8115890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115890).length < 2 ^ (prefixWord ++ tailWord_8115890).sum := by decide
  have hdescent : baseEnd_8115890 < baseStart_8115890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115897 : List Nat := [1, 2, 1, 4, 1, 1, 2, 5, 1, 1, 4]
def baseStart_8115897 : Nat := 118140960795 + 8115897 * 2 ^ 59
def prefixEnd_8115897 : Nat := 4983230072969 + 3 ^ 40 * 8115897 * 2
def baseEnd_8115897 : Nat := 4167356103382938249363175

theorem tailTrace_8115897 : CollatzResearch.WordTrace tailWord_8115897 prefixEnd_8115897 4167356103382938249363175 := by
  unfold tailWord_8115897
  simp only [CollatzResearch.WordTrace]
  refine ⟨296011081878498728700857945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197340721252332485800571963 296011081878498728700857945)
  ·
    refine ⟨222008311408874046525643459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296011081878498728700857945 222008311408874046525643459)
    ·
      refine ⟨333012467113311069788465189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222008311408874046525643459 333012467113311069788465189)
      ·
        refine ⟨62439837583745825585337223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333012467113311069788465189 62439837583745825585337223)
        ·
          refine ⟨93659756375618738378005835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62439837583745825585337223 93659756375618738378005835)
          ·
            refine ⟨140489634563428107567008753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93659756375618738378005835 140489634563428107567008753)
            ·
              refine ⟨105367225922571080675256565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140489634563428107567008753 105367225922571080675256565)
              ·
                refine ⟨9878177430241038813305303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105367225922571080675256565 9878177430241038813305303)
                ·
                  refine ⟨14817266145361558219957955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9878177430241038813305303 14817266145361558219957955)
                  ·
                    refine ⟨22225899218042337329936933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14817266145361558219957955 22225899218042337329936933)
                    ·
                      refine ⟨4167356103382938249363175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22225899218042337329936933 4167356103382938249363175)
                      ·
                        rfl

theorem cell23_8115897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_8115897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115897 prefixEnd_8115897 := by exact prefixLift 8115897
  have htrace : WordTrace (prefixWord ++ tailWord_8115897) baseStart_8115897 baseEnd_8115897 := by
    simpa [prefixWord, tailWord_8115897, baseEnd_8115897] using wordTrace_append hprefix tailTrace_8115897
  have hstable : (prefixWord ++ tailWord_8115897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115897).length < 2 ^ (prefixWord ++ tailWord_8115897).sum := by decide
  have hdescent : baseEnd_8115897 < baseStart_8115897 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115924 : List Nat := [2, 4, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_8115924 : Nat := 118140960795 + 8115924 * 2 ^ 59
def prefixEnd_8115924 : Nat := 4983230072969 + 3 ^ 40 * 8115924 * 2
def baseEnd_8115924 : Nat := 1389123322453536547908517

theorem tailTrace_8115924 : CollatzResearch.WordTrace tailWord_8115924 prefixEnd_8115924 1389123322453536547908517 := by
  unfold tailWord_8115924
  simp only [CollatzResearch.WordTrace]
  refine ⟨148006033324700456156045413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197341377766267274874727217 148006033324700456156045413)
  ·
    refine ⟨27751131248381335529258515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148006033324700456156045413 27751131248381335529258515)
    ·
      refine ⟨41626696872572003293887773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27751131248381335529258515 41626696872572003293887773)
      ·
        refine ⟨15610011327214501235207915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41626696872572003293887773 15610011327214501235207915)
        ·
          refine ⟨23415016990821751852811873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15610011327214501235207915 23415016990821751852811873)
          ·
            refine ⟨17561262743116313889608905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23415016990821751852811873 17561262743116313889608905)
            ·
              refine ⟨13170947057337235417206679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17561262743116313889608905 13170947057337235417206679)
              ·
                refine ⟨19756420586005853125810019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13170947057337235417206679 19756420586005853125810019)
                ·
                  refine ⟨29634630879008779688715029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19756420586005853125810019 29634630879008779688715029)
                  ·
                    refine ⟨1389123322453536547908517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29634630879008779688715029 1389123322453536547908517)
                    ·
                      rfl

theorem cell23_8115924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_8115924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115924 prefixEnd_8115924 := by exact prefixLift 8115924
  have htrace : WordTrace (prefixWord ++ tailWord_8115924) baseStart_8115924 baseEnd_8115924 := by
    simpa [prefixWord, tailWord_8115924, baseEnd_8115924] using wordTrace_append hprefix tailTrace_8115924
  have hstable : (prefixWord ++ tailWord_8115924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115924).length < 2 ^ (prefixWord ++ tailWord_8115924).sum := by decide
  have hdescent : baseEnd_8115924 < baseStart_8115924 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115927 : List Nat := [1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 4]
def baseStart_8115927 : Nat := 118140960795 + 8115927 * 2 ^ 59
def prefixEnd_8115927 : Nat := 4983230072969 + 3 ^ 40 * 8115927 * 2
def baseEnd_8115927 : Nat := 4167371507802573131988037

theorem tailTrace_8115927 : CollatzResearch.WordTrace tailWord_8115927 prefixEnd_8115927 4167371507802573131988037 := by
  unfold tailWord_8115927
  simp only [CollatzResearch.WordTrace]
  refine ⟨296012176068390043824450035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197341450712260029216300023 296012176068390043824450035)
  ·
    refine ⟨444018264102585065736675053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296012176068390043824450035 444018264102585065736675053)
    ·
      refine ⟨166506849038469399651253145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444018264102585065736675053 166506849038469399651253145)
      ·
        refine ⟨124880136778852049738439859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166506849038469399651253145 124880136778852049738439859)
        ·
          refine ⟨187320205168278074607659789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124880136778852049738439859 187320205168278074607659789)
          ·
            refine ⟨70245076938104277977872421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187320205168278074607659789 70245076938104277977872421)
            ·
              refine ⟨13170951925894552120851079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70245076938104277977872421 13170951925894552120851079)
              ·
                refine ⟨19756427888841828181276619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13170951925894552120851079 19756427888841828181276619)
                ·
                  refine ⟨29634641833262742271914929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19756427888841828181276619 29634641833262742271914929)
                  ·
                    refine ⟨22225981374947056703936197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29634641833262742271914929 22225981374947056703936197)
                    ·
                      refine ⟨4167371507802573131988037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22225981374947056703936197 4167371507802573131988037)
                      ·
                        rfl

theorem cell23_8115927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_8115927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115927 prefixEnd_8115927 := by exact prefixLift 8115927
  have htrace : WordTrace (prefixWord ++ tailWord_8115927) baseStart_8115927 baseEnd_8115927 := by
    simpa [prefixWord, tailWord_8115927, baseEnd_8115927] using wordTrace_append hprefix tailTrace_8115927
  have hstable : (prefixWord ++ tailWord_8115927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115927).length < 2 ^ (prefixWord ++ tailWord_8115927).sum := by decide
  have hdescent : baseEnd_8115927 < baseStart_8115927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115947 : List Nat := [1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 3]
def baseStart_8115947 : Nat := 118140960795 + 8115947 * 2 ^ 59
def prefixEnd_8115947 : Nat := 4983230072969 + 3 ^ 40 * 8115947 * 2
def baseEnd_8115947 : Nat := 4167381777415663053737945

theorem tailTrace_8115947 : CollatzResearch.WordTrace tailWord_8115947 prefixEnd_8115947 4167381777415663053737945 := by
  unfold tailWord_8115947
  simp only [CollatzResearch.WordTrace]
  refine ⟨296012905528317587240178095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197341937018878391493452063 296012905528317587240178095)
  ·
    refine ⟨444019358292476380860267143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296012905528317587240178095 444019358292476380860267143)
    ·
      refine ⟨666029037438714571290400715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444019358292476380860267143 666029037438714571290400715)
      ·
        refine ⟨999043556158071856935601073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666029037438714571290400715 999043556158071856935601073)
        ·
          refine ⟨749282667118553892701700805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 999043556158071856935601073 749282667118553892701700805)
          ·
            refine ⟨140490500084728854881568901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 749282667118553892701700805 140490500084728854881568901)
            ·
              refine ⟨26341968765886660290294169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140490500084728854881568901 26341968765886660290294169)
              ·
                refine ⟨19756476574414995217720627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26341968765886660290294169 19756476574414995217720627)
                ·
                  refine ⟨29634714861622492826580941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19756476574414995217720627 29634714861622492826580941)
                  ·
                    refine ⟨11113018073108434809967853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29634714861622492826580941 11113018073108434809967853)
                    ·
                      refine ⟨4167381777415663053737945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11113018073108434809967853 4167381777415663053737945)
                      ·
                        rfl

theorem cell23_8115947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 3].length) (baseStart_8115947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115947 prefixEnd_8115947 := by exact prefixLift 8115947
  have htrace : WordTrace (prefixWord ++ tailWord_8115947) baseStart_8115947 baseEnd_8115947 := by
    simpa [prefixWord, tailWord_8115947, baseEnd_8115947] using wordTrace_append hprefix tailTrace_8115947
  have hstable : (prefixWord ++ tailWord_8115947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115947).length < 2 ^ (prefixWord ++ tailWord_8115947).sum := by decide
  have hdescent : baseEnd_8115947 < baseStart_8115947 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115960 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 4, 2, 5]
def baseStart_8115960 : Nat := 118140960795 + 8115960 * 2 ^ 59
def prefixEnd_8115960 : Nat := 4983230072969 + 3 ^ 40 * 8115960 * 2
def baseEnd_8115960 : Nat := 4167388452664171502875385

theorem tailTrace_8115960 : CollatzResearch.WordTrace tailWord_8115960 prefixEnd_8115960 4167388452664171502875385 := by
  unfold tailWord_8115960
  simp only [CollatzResearch.WordTrace]
  refine ⟨148006689838635245230200667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197342253118180326973600889 148006689838635245230200667)
  ·
    refine ⟨222010034757952867845301001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148006689838635245230200667 222010034757952867845301001)
    ·
      refine ⟨166507526068464650883975751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222010034757952867845301001 166507526068464650883975751)
      ·
        refine ⟨249761289102696976325963627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166507526068464650883975751 249761289102696976325963627)
        ·
          refine ⟨374641933654045464488945441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249761289102696976325963627 374641933654045464488945441)
          ·
            refine ⟨280981450240534098366709081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374641933654045464488945441 280981450240534098366709081)
            ·
              refine ⟨210736087680400573775031811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280981450240534098366709081 210736087680400573775031811)
              ·
                refine ⟨316104131520600860662547717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210736087680400573775031811 316104131520600860662547717)
                ·
                  refine ⟨59269524660112661374227697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316104131520600860662547717 59269524660112661374227697)
                  ·
                    refine ⟨44452143495084496030670773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59269524660112661374227697 44452143495084496030670773)
                    ·
                      refine ⟨4167388452664171502875385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44452143495084496030670773 4167388452664171502875385)
                      ·
                        rfl

theorem cell23_8115960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_8115960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115960 prefixEnd_8115960 := by exact prefixLift 8115960
  have htrace : WordTrace (prefixWord ++ tailWord_8115960) baseStart_8115960 baseEnd_8115960 := by
    simpa [prefixWord, tailWord_8115960, baseEnd_8115960] using wordTrace_append hprefix tailTrace_8115960
  have hstable : (prefixWord ++ tailWord_8115960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115960).length < 2 ^ (prefixWord ++ tailWord_8115960).sum := by decide
  have hdescent : baseEnd_8115960 < baseStart_8115960 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115964 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 4, 1, 3]
def baseStart_8115964 : Nat := 118140960795 + 8115964 * 2 ^ 59
def prefixEnd_8115964 : Nat := 4983230072969 + 3 ^ 40 * 8115964 * 2
def baseEnd_8115964 : Nat := 4167390506586789487225367

theorem tailTrace_8115964 : CollatzResearch.WordTrace tailWord_8115964 prefixEnd_8115964 4167390506586789487225367 := by
  unfold tailWord_8115964
  simp only [CollatzResearch.WordTrace]
  refine ⟨148006762784627999571773473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197342350379503999429031297 148006762784627999571773473)
  ·
    refine ⟨111005072088470999678830105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148006762784627999571773473 111005072088470999678830105)
    ·
      refine ⟨83253804066353249759122579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111005072088470999678830105 83253804066353249759122579)
      ·
        refine ⟨124880706099529874638683869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83253804066353249759122579 124880706099529874638683869)
        ·
          refine ⟨46830264787323702989506451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124880706099529874638683869 46830264787323702989506451)
          ·
            refine ⟨70245397180985554484259677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46830264787323702989506451 70245397180985554484259677)
            ·
              refine ⟨26342023942869582931597379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70245397180985554484259677 26342023942869582931597379)
              ·
                refine ⟨39513035914304374397396069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26342023942869582931597379 39513035914304374397396069)
                ·
                  refine ⟨7408694233932070199511763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39513035914304374397396069 7408694233932070199511763)
                  ·
                    refine ⟨11113041350898105299267645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7408694233932070199511763 11113041350898105299267645)
                    ·
                      refine ⟨4167390506586789487225367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11113041350898105299267645 4167390506586789487225367)
                      ·
                        rfl

theorem cell23_8115964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_8115964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115964 prefixEnd_8115964 := by exact prefixLift 8115964
  have htrace : WordTrace (prefixWord ++ tailWord_8115964) baseStart_8115964 baseEnd_8115964 := by
    simpa [prefixWord, tailWord_8115964, baseEnd_8115964] using wordTrace_append hprefix tailTrace_8115964
  have hstable : (prefixWord ++ tailWord_8115964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115964).length < 2 ^ (prefixWord ++ tailWord_8115964).sum := by decide
  have hdescent : baseEnd_8115964 < baseStart_8115964 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8115991 : List Nat := [1, 1, 3, 4, 2, 1, 1, 4, 1, 3, 2]
def baseStart_8115991 : Nat := 118140960795 + 8115991 * 2 ^ 59
def prefixEnd_8115991 : Nat := 4983230072969 + 3 ^ 40 * 8115991 * 2
def baseEnd_8115991 : Nat := 4167404370564460881587743

theorem tailTrace_8115991 : CollatzResearch.WordTrace tailWord_8115991 prefixEnd_8115991 4167404370564460881587743 := by
  unfold tailWord_8115991
  simp only [CollatzResearch.WordTrace]
  refine ⟨296014510340158182754779827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197343006893438788503186551 296014510340158182754779827)
  ·
    refine ⟨444021765510237274132169741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296014510340158182754779827 444021765510237274132169741)
    ·
      refine ⟨166508162066338977799563653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444021765510237274132169741 166508162066338977799563653)
      ·
        refine ⟨31220280387438558337418185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166508162066338977799563653 31220280387438558337418185)
        ·
          refine ⟨23415210290578918753063639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31220280387438558337418185 23415210290578918753063639)
          ·
            refine ⟨35122815435868378129595459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23415210290578918753063639 35122815435868378129595459)
            ·
              refine ⟨52684223153802567194393189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35122815435868378129595459 52684223153802567194393189)
              ·
                refine ⟨9878291841337981348948723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52684223153802567194393189 9878291841337981348948723)
                ·
                  refine ⟨14817437762006972023423085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9878291841337981348948723 14817437762006972023423085)
                  ·
                    refine ⟨5556539160752614508783657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14817437762006972023423085 5556539160752614508783657)
                    ·
                      refine ⟨4167404370564460881587743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5556539160752614508783657 4167404370564460881587743)
                      ·
                        rfl

theorem cell23_8115991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_8115991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8115991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8115991 prefixEnd_8115991 := by exact prefixLift 8115991
  have htrace : WordTrace (prefixWord ++ tailWord_8115991) baseStart_8115991 baseEnd_8115991 := by
    simpa [prefixWord, tailWord_8115991, baseEnd_8115991] using wordTrace_append hprefix tailTrace_8115991
  have hstable : (prefixWord ++ tailWord_8115991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8115991).length < 2 ^ (prefixWord ++ tailWord_8115991).sum := by decide
  have hdescent : baseEnd_8115991 < baseStart_8115991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8115991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116037 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 1, 5, 3]
def baseStart_8116037 : Nat := 118140960795 + 8116037 * 2 ^ 59
def prefixEnd_8116037 : Nat := 4983230072969 + 3 ^ 40 * 8116037 * 2
def baseEnd_8116037 : Nat := 4167427990674567701612531

theorem tailTrace_8116037 : CollatzResearch.WordTrace tailWord_8116037 prefixEnd_8116037 4167427990674567701612531 := by
  unfold tailWord_8116037
  simp only [CollatzResearch.WordTrace]
  refine ⟨296016188097991532610954365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197344125398661021740636243 296016188097991532610954365)
  ·
    refine ⟨111006070536746824729107887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296016188097991532610954365 111006070536746824729107887)
    ·
      refine ⟨166509105805120237093661831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111006070536746824729107887 166509105805120237093661831)
      ·
        refine ⟨249763658707680355640492747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166509105805120237093661831 249763658707680355640492747)
        ·
          refine ⟨374645488061520533460739121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249763658707680355640492747 374645488061520533460739121)
          ·
            refine ⟨280984116046140400095554341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374645488061520533460739121 280984116046140400095554341)
            ·
              refine ⟨52684521758651325017916439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280984116046140400095554341 52684521758651325017916439)
              ·
                refine ⟨79026782637976987526874659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52684521758651325017916439 79026782637976987526874659)
                ·
                  refine ⟨118540173956965481290311989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79026782637976987526874659 118540173956965481290311989)
                  ·
                    refine ⟨11113141308465513870966749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118540173956965481290311989 11113141308465513870966749)
                    ·
                      refine ⟨4167427990674567701612531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11113141308465513870966749 4167427990674567701612531)
                      ·
                        rfl

theorem cell23_8116037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_8116037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116037 prefixEnd_8116037 := by exact prefixLift 8116037
  have htrace : WordTrace (prefixWord ++ tailWord_8116037) baseStart_8116037 baseEnd_8116037 := by
    simpa [prefixWord, tailWord_8116037, baseEnd_8116037] using wordTrace_append hprefix tailTrace_8116037
  have hstable : (prefixWord ++ tailWord_8116037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116037).length < 2 ^ (prefixWord ++ tailWord_8116037).sum := by decide
  have hdescent : baseEnd_8116037 < baseStart_8116037 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116078 : List Nat := [4, 1, 2, 3, 1, 1, 4, 2, 5]
def baseStart_8116078 : Nat := 118140960795 + 8116078 * 2 ^ 59
def prefixEnd_8116078 : Nat := 4983230072969 + 3 ^ 40 * 8116078 * 2
def baseEnd_8116078 : Nat := 463049893709044671244427

theorem tailTrace_8116078 : CollatzResearch.WordTrace tailWord_8116078 prefixEnd_8116078 463049893709044671244427 := by
  unfold tailWord_8116078
  simp only [CollatzResearch.WordTrace]
  refine ⟨37002210436355374576649611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197345122327228664408797925 37002210436355374576649611)
  ·
    refine ⟨55503315654533061864974417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37002210436355374576649611 55503315654533061864974417)
    ·
      refine ⟨41627486740899796398730813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55503315654533061864974417 41627486740899796398730813)
      ·
        refine ⟨15610307527837423649524055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41627486740899796398730813 15610307527837423649524055)
        ·
          refine ⟨23415461291756135474286083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15610307527837423649524055 23415461291756135474286083)
          ·
            refine ⟨35123191937634203211429125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23415461291756135474286083 35123191937634203211429125)
            ·
              refine ⟨6585598488306413102142961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35123191937634203211429125 6585598488306413102142961)
              ·
                refine ⟨4939198866229809826607221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6585598488306413102142961 4939198866229809826607221)
                ·
                  refine ⟨463049893709044671244427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4939198866229809826607221 463049893709044671244427)
                  ·
                    rfl

theorem cell23_8116078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_8116078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116078 prefixEnd_8116078 := by exact prefixLift 8116078
  have htrace : WordTrace (prefixWord ++ tailWord_8116078) baseStart_8116078 baseEnd_8116078 := by
    simpa [prefixWord, tailWord_8116078, baseEnd_8116078] using wordTrace_append hprefix tailTrace_8116078
  have hstable : (prefixWord ++ tailWord_8116078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116078).length < 2 ^ (prefixWord ++ tailWord_8116078).sum := by decide
  have hdescent : baseEnd_8116078 < baseStart_8116078 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116117 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 8]
def baseStart_8116117 : Nat := 118140960795 + 8116117 * 2 ^ 59
def prefixEnd_8116117 : Nat := 4983230072969 + 3 ^ 40 * 8116117 * 2
def baseEnd_8116117 : Nat := 463052118791880820956907

theorem tailTrace_8116117 : CollatzResearch.WordTrace tailWord_8116117 prefixEnd_8116117 463052118791880820956907 := by
  unfold tailWord_8116117
  simp only [CollatzResearch.WordTrace]
  refine ⟨296019105937701706273866605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197346070625134470849244403 296019105937701706273866605)
  ·
    refine ⟨111007164726638139852699977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296019105937701706273866605 111007164726638139852699977)
    ·
      refine ⟨83255373544978604889524983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111007164726638139852699977 83255373544978604889524983)
      ·
        refine ⟨124883060317467907334287475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83255373544978604889524983 124883060317467907334287475)
        ·
          refine ⟨187324590476201861001431213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124883060317467907334287475 187324590476201861001431213)
          ·
            refine ⟨70246721428575697875536705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187324590476201861001431213 70246721428575697875536705)
            ·
              refine ⟨52685041071431773406652529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70246721428575697875536705 52685041071431773406652529)
              ·
                refine ⟨39513780803573830054989397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52685041071431773406652529 39513780803573830054989397)
                ·
                  refine ⟨463052118791880820956907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39513780803573830054989397 463052118791880820956907)
                  ·
                    rfl

theorem cell23_8116117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 8].length) (baseStart_8116117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116117 prefixEnd_8116117 := by exact prefixLift 8116117
  have htrace : WordTrace (prefixWord ++ tailWord_8116117) baseStart_8116117 baseEnd_8116117 := by
    simpa [prefixWord, tailWord_8116117, baseEnd_8116117] using wordTrace_append hprefix tailTrace_8116117
  have hstable : (prefixWord ++ tailWord_8116117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116117).length < 2 ^ (prefixWord ++ tailWord_8116117).sum := by decide
  have hdescent : baseEnd_8116117 < baseStart_8116117 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116121 : List Nat := [1, 2, 1, 2, 1, 3, 3, 5, 1, 4]
def baseStart_8116121 : Nat := 118140960795 + 8116121 * 2 ^ 59
def prefixEnd_8116121 : Nat := 4983230072969 + 3 ^ 40 * 8116121 * 2
def baseEnd_8116121 : Nat := 1389157041016515124320715

theorem tailTrace_8116121 : CollatzResearch.WordTrace tailWord_8116121 prefixEnd_8116121 1389157041016515124320715 := by
  unfold tailWord_8116121
  simp only [CollatzResearch.WordTrace]
  refine ⟨296019251829687214957012217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197346167886458143304674811 296019251829687214957012217)
  ·
    refine ⟨222014438872265411217759163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296019251829687214957012217 222014438872265411217759163)
    ·
      refine ⟨333021658308398116826638745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222014438872265411217759163 333021658308398116826638745)
      ·
        refine ⟨249766243731298587619979059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333021658308398116826638745 249766243731298587619979059)
        ·
          refine ⟨374649365596947881429968589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249766243731298587619979059 374649365596947881429968589)
          ·
            refine ⟨140493512098855455536238221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374649365596947881429968589 140493512098855455536238221)
            ·
              refine ⟨52685067037070795826089333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140493512098855455536238221 52685067037070795826089333)
              ·
                refine ⟨4939225034725387108695875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52685067037070795826089333 4939225034725387108695875)
                ·
                  refine ⟨7408837552088080663043813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4939225034725387108695875 7408837552088080663043813)
                  ·
                    refine ⟨1389157041016515124320715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7408837552088080663043813 1389157041016515124320715)
                    ·
                      rfl

theorem cell23_8116121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 1, 4].length) (baseStart_8116121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116121 prefixEnd_8116121 := by exact prefixLift 8116121
  have htrace : WordTrace (prefixWord ++ tailWord_8116121) baseStart_8116121 baseEnd_8116121 := by
    simpa [prefixWord, tailWord_8116121, baseEnd_8116121] using wordTrace_append hprefix tailTrace_8116121
  have hstable : (prefixWord ++ tailWord_8116121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116121).length < 2 ^ (prefixWord ++ tailWord_8116121).sum := by decide
  have hdescent : baseEnd_8116121 < baseStart_8116121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116124 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_8116124 : Nat := 118140960795 + 8116124 * 2 ^ 59
def prefixEnd_8116124 : Nat := 4983230072969 + 3 ^ 40 * 8116124 * 2
def baseEnd_8116124 : Nat := 4167472663491508861224631

theorem tailTrace_8116124 : CollatzResearch.WordTrace tailWord_8116124 prefixEnd_8116124 4167472663491508861224631 := by
  unfold tailWord_8116124
  simp only [CollatzResearch.WordTrace]
  refine ⟨148009680624338173234685713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197346240832450897646247617 148009680624338173234685713)
  ·
    refine ⟨111007260468253629926014285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148009680624338173234685713 111007260468253629926014285)
    ·
      refine ⟨41627722675595111222255357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111007260468253629926014285 41627722675595111222255357)
      ·
        refine ⟨15610396003348166708345759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41627722675595111222255357 15610396003348166708345759)
        ·
          refine ⟨23415594005022250062518639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15610396003348166708345759 23415594005022250062518639)
          ·
            refine ⟨35123391007533375093777959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23415594005022250062518639 35123391007533375093777959)
            ·
              refine ⟨52685086511300062640666939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35123391007533375093777959 52685086511300062640666939)
              ·
                refine ⟨79027629766950093961000409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52685086511300062640666939 79027629766950093961000409)
                ·
                  refine ⟨59270722325212570470750307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79027629766950093961000409 59270722325212570470750307)
                  ·
                    refine ⟨88906083487818855706125461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59270722325212570470750307 88906083487818855706125461)
                    ·
                      refine ⟨4167472663491508861224631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88906083487818855706125461 4167472663491508861224631)
                      ·
                        rfl

theorem cell23_8116124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_8116124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116124 prefixEnd_8116124 := by exact prefixLift 8116124
  have htrace : WordTrace (prefixWord ++ tailWord_8116124) baseStart_8116124 baseEnd_8116124 := by
    simpa [prefixWord, tailWord_8116124, baseEnd_8116124] using wordTrace_append hprefix tailTrace_8116124
  have hstable : (prefixWord ++ tailWord_8116124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116124).length < 2 ^ (prefixWord ++ tailWord_8116124).sum := by decide
  have hdescent : baseEnd_8116124 < baseStart_8116124 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116171 : List Nat := [1, 1, 1, 1, 3, 4, 2, 3, 2, 3, 2]
def baseStart_8116171 : Nat := 118140960795 + 8116171 * 2 ^ 59
def prefixEnd_8116171 : Nat := 4983230072969 + 3 ^ 40 * 8116171 * 2
def baseEnd_8116171 : Nat := 4167496797082270177336915

theorem tailTrace_8116171 : CollatzResearch.WordTrace tailWord_8116171 prefixEnd_8116171 4167496797082270177336915 := by
  unfold tailWord_8116171
  simp only [CollatzResearch.WordTrace]
  refine ⟨296021075479506073496332367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197347383653004048997554911 296021075479506073496332367)
  ·
    refine ⟨444031613219259110244498551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296021075479506073496332367 444031613219259110244498551)
    ·
      refine ⟨666047419828888665366747827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444031613219259110244498551 666047419828888665366747827)
      ·
        refine ⟨999071129743332998050121741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666047419828888665366747827 999071129743332998050121741)
        ·
          refine ⟨374651673653749874268795653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 999071129743332998050121741 374651673653749874268795653)
          ·
            refine ⟨70247188810078101425399185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 374651673653749874268795653 70247188810078101425399185)
            ·
              refine ⟨52685391607558576069049389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70247188810078101425399185 52685391607558576069049389)
              ·
                refine ⟨19757021852834466025893521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52685391607558576069049389 19757021852834466025893521)
                ·
                  refine ⟨14817766389625849519420141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19757021852834466025893521 14817766389625849519420141)
                  ·
                    refine ⟨5556662396109693569782553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14817766389625849519420141 5556662396109693569782553)
                    ·
                      refine ⟨4167496797082270177336915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5556662396109693569782553 4167496797082270177336915)
                      ·
                        rfl

theorem cell23_8116171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 3, 2].length) (baseStart_8116171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116171 prefixEnd_8116171 := by exact prefixLift 8116171
  have htrace : WordTrace (prefixWord ++ tailWord_8116171) baseStart_8116171 baseEnd_8116171 := by
    simpa [prefixWord, tailWord_8116171, baseEnd_8116171] using wordTrace_append hprefix tailTrace_8116171
  have hstable : (prefixWord ++ tailWord_8116171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116171).length < 2 ^ (prefixWord ++ tailWord_8116171).sum := by decide
  have hdescent : baseEnd_8116171 < baseStart_8116171 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116181 : List Nat := [1, 3, 2, 3, 2, 1, 2, 3, 1, 5]
def baseStart_8116181 : Nat := 118140960795 + 8116181 * 2 ^ 59
def prefixEnd_8116181 : Nat := 4983230072969 + 3 ^ 40 * 8116181 * 2
def baseEnd_8116181 : Nat := 1389167310629605046070623

theorem tailTrace_8116181 : CollatzResearch.WordTrace tailWord_8116181 prefixEnd_8116181 1389167310629605046070623 := by
  unfold tailWord_8116181
  simp only [CollatzResearch.WordTrace]
  refine ⟨296021440209469845204196397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197347626806313230136130931 296021440209469845204196397)
  ·
    refine ⟨111008040078551191951573649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296021440209469845204196397 111008040078551191951573649)
    ·
      refine ⟨83256030058913393963680237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111008040078551191951573649 83256030058913393963680237)
      ·
        refine ⟨31221011272092522736380089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83256030058913393963680237 31221011272092522736380089)
        ·
          refine ⟨23415758454069392052285067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31221011272092522736380089 23415758454069392052285067)
          ·
            refine ⟨35123637681104088078427601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23415758454069392052285067 35123637681104088078427601)
            ·
              refine ⟨26342728260828066058820701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35123637681104088078427601 26342728260828066058820701)
              ·
                refine ⟨9878523097810524772057763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26342728260828066058820701 9878523097810524772057763)
                ·
                  refine ⟨14817784646715787158086645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9878523097810524772057763 14817784646715787158086645)
                  ·
                    refine ⟨1389167310629605046070623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14817784646715787158086645 1389167310629605046070623)
                    ·
                      rfl

theorem cell23_8116181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_8116181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116181 prefixEnd_8116181 := by exact prefixLift 8116181
  have htrace : WordTrace (prefixWord ++ tailWord_8116181) baseStart_8116181 baseEnd_8116181 := by
    simpa [prefixWord, tailWord_8116181, baseEnd_8116181] using wordTrace_append hprefix tailTrace_8116181
  have hstable : (prefixWord ++ tailWord_8116181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116181).length < 2 ^ (prefixWord ++ tailWord_8116181).sum := by decide
  have hdescent : baseEnd_8116181 < baseStart_8116181 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116228 : List Nat := [2, 3, 2, 4, 1, 1, 1, 2, 1, 6]
def baseStart_8116228 : Nat := 118140960795 + 8116228 * 2 ^ 59
def prefixEnd_8116228 : Nat := 4983230072969 + 3 ^ 40 * 8116228 * 2
def baseEnd_8116228 : Nat := 1389175355159858818108051

theorem tailTrace_8116228 : CollatzResearch.WordTrace tailWord_8116228 prefixEnd_8116228 1389175355159858818108051 := by
  unfold tailWord_8116228
  simp only [CollatzResearch.WordTrace]
  refine ⟨148011577220149786115578669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197348769626866381487438225 148011577220149786115578669)
  ·
    refine ⟨55504341457556169793342001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148011577220149786115578669 55504341457556169793342001)
    ·
      refine ⟨41628256093167127345006501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55504341457556169793342001 41628256093167127345006501)
      ·
        refine ⟨7805298017468836377188719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41628256093167127345006501 7805298017468836377188719)
        ·
          refine ⟨11707947026203254565783079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7805298017468836377188719 11707947026203254565783079)
          ·
            refine ⟨17561920539304881848674619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11707947026203254565783079 17561920539304881848674619)
            ·
              refine ⟨26342880808957322773011929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17561920539304881848674619 26342880808957322773011929)
              ·
                refine ⟨19757160606717992079758947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26342880808957322773011929 19757160606717992079758947)
                ·
                  refine ⟨29635740910076988119638421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19757160606717992079758947 29635740910076988119638421)
                  ·
                    refine ⟨1389175355159858818108051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29635740910076988119638421 1389175355159858818108051)
                    ·
                      rfl

theorem cell23_8116228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_8116228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116228 prefixEnd_8116228 := by exact prefixLift 8116228
  have htrace : WordTrace (prefixWord ++ tailWord_8116228) baseStart_8116228 baseEnd_8116228 := by
    simpa [prefixWord, tailWord_8116228, baseEnd_8116228] using wordTrace_append hprefix tailTrace_8116228
  have hstable : (prefixWord ++ tailWord_8116228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116228).length < 2 ^ (prefixWord ++ tailWord_8116228).sum := by decide
  have hdescent : baseEnd_8116228 < baseStart_8116228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116231 : List Nat := [1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_8116231 : Nat := 118140960795 + 8116231 * 2 ^ 59
def prefixEnd_8116231 : Nat := 4983230072969 + 3 ^ 40 * 8116231 * 2
def baseEnd_8116231 : Nat := 4167527605921539942586639

theorem tailTrace_8116231 : CollatzResearch.WordTrace tailWord_8116231 prefixEnd_8116231 4167527605921539942586639 := by
  unfold tailWord_8116231
  simp only [CollatzResearch.WordTrace]
  refine ⟨296023263859288703743516547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197348842572859135829011031 296023263859288703743516547)
  ·
    refine ⟨444034895788933055615274821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296023263859288703743516547 444034895788933055615274821)
    ·
      refine ⟨83256542960424947927864029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 444034895788933055615274821 83256542960424947927864029)
      ·
        refine ⟨31221203610159355472949011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83256542960424947927864029 31221203610159355472949011)
        ·
          refine ⟨46831805415239033209423517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31221203610159355472949011 46831805415239033209423517)
          ·
            refine ⟨17561927030714637453533819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46831805415239033209423517 17561927030714637453533819)
            ·
              refine ⟨26342890546071956180300729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17561927030714637453533819 26342890546071956180300729)
              ·
                refine ⟨19757167909553967135225547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26342890546071956180300729 19757167909553967135225547)
                ·
                  refine ⟨29635751864330950702838321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19757167909553967135225547 29635751864330950702838321)
                  ·
                    refine ⟨22226813898248213027128741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29635751864330950702838321 22226813898248213027128741)
                    ·
                      refine ⟨4167527605921539942586639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22226813898248213027128741 4167527605921539942586639)
                      ·
                        rfl

theorem cell23_8116231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_8116231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116231 prefixEnd_8116231 := by exact prefixLift 8116231
  have htrace : WordTrace (prefixWord ++ tailWord_8116231) baseStart_8116231 baseEnd_8116231 := by
    simpa [prefixWord, tailWord_8116231, baseEnd_8116231] using wordTrace_append hprefix tailTrace_8116231
  have hstable : (prefixWord ++ tailWord_8116231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116231).length < 2 ^ (prefixWord ++ tailWord_8116231).sum := by decide
  have hdescent : baseEnd_8116231 < baseStart_8116231 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116235 : List Nat := [1, 1, 1, 1, 6, 1, 2, 5, 1, 2, 2]
def baseStart_8116235 : Nat := 118140960795 + 8116235 * 2 ^ 59
def prefixEnd_8116235 : Nat := 4983230072969 + 3 ^ 40 * 8116235 * 2
def baseEnd_8116235 : Nat := 4167529659844157926936621

theorem tailTrace_8116235 : CollatzResearch.WordTrace tailWord_8116235 prefixEnd_8116235 4167529659844157926936621 := by
  unfold tailWord_8116235
  simp only [CollatzResearch.WordTrace]
  refine ⟨296023409751274212426662159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197348939834182808284441439 296023409751274212426662159)
  ·
    refine ⟨444035114626911318639993239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296023409751274212426662159 444035114626911318639993239)
    ·
      refine ⟨666052671940366977959989859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444035114626911318639993239 666052671940366977959989859)
      ·
        refine ⟨999079007910550466939984789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666052671940366977959989859 999079007910550466939984789)
        ·
          refine ⟨46831828495807053137811787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 999079007910550466939984789 46831828495807053137811787)
          ·
            refine ⟨70247742743710579706717681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46831828495807053137811787 70247742743710579706717681)
            ·
              refine ⟨52685807057782934780038261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70247742743710579706717681 52685807057782934780038261)
              ·
                refine ⟨4939294411667150135628587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52685807057782934780038261 4939294411667150135628587)
                ·
                  refine ⟨7408941617500725203442881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4939294411667150135628587 7408941617500725203442881)
                  ·
                    refine ⟨5556706213125543902582161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7408941617500725203442881 5556706213125543902582161)
                    ·
                      refine ⟨4167529659844157926936621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5556706213125543902582161 4167529659844157926936621)
                      ·
                        rfl

theorem cell23_8116235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 1, 2, 2].length) (baseStart_8116235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116235 prefixEnd_8116235 := by exact prefixLift 8116235
  have htrace : WordTrace (prefixWord ++ tailWord_8116235) baseStart_8116235 baseEnd_8116235 := by
    simpa [prefixWord, tailWord_8116235, baseEnd_8116235] using wordTrace_append hprefix tailTrace_8116235
  have hstable : (prefixWord ++ tailWord_8116235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116235).length < 2 ^ (prefixWord ++ tailWord_8116235).sum := by decide
  have hdescent : baseEnd_8116235 < baseStart_8116235 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116252 : List Nat := [2, 2, 3, 1, 3, 2, 1, 4, 1, 2, 2]
def baseStart_8116252 : Nat := 118140960795 + 8116252 * 2 ^ 59
def prefixEnd_8116252 : Nat := 4983230072969 + 3 ^ 40 * 8116252 * 2
def baseEnd_8116252 : Nat := 4167538389015284360424043

theorem tailTrace_8116252 : CollatzResearch.WordTrace tailWord_8116252 prefixEnd_8116252 4167538389015284360424043 := by
  unfold tailWord_8116252
  simp only [CollatzResearch.WordTrace]
  refine ⟨148012014896106312165015505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197349353194808416220020673 148012014896106312165015505)
  ·
    refine ⟨111009011172079734123761629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148012014896106312165015505 111009011172079734123761629)
    ·
      refine ⟨41628379189529900296410611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111009011172079734123761629 41628379189529900296410611)
      ·
        refine ⟨62442568784294850444615917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41628379189529900296410611 62442568784294850444615917)
        ·
          refine ⟨23415963294110568916730969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62442568784294850444615917 23415963294110568916730969)
          ·
            refine ⟨17561972470582926687548227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23415963294110568916730969 17561972470582926687548227)
            ·
              refine ⟨26342958705874390031322341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17561972470582926687548227 26342958705874390031322341)
              ·
                refine ⟨4939304757351448130872939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26342958705874390031322341 4939304757351448130872939)
                ·
                  refine ⟨7408957136027172196309409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4939304757351448130872939 7408957136027172196309409)
                  ·
                    refine ⟨5556717852020379147232057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7408957136027172196309409 5556717852020379147232057)
                    ·
                      refine ⟨4167538389015284360424043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5556717852020379147232057 4167538389015284360424043)
                      ·
                        rfl

theorem cell23_8116252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_8116252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116252 prefixEnd_8116252 := by exact prefixLift 8116252
  have htrace : WordTrace (prefixWord ++ tailWord_8116252) baseStart_8116252 baseEnd_8116252 := by
    simpa [prefixWord, tailWord_8116252, baseEnd_8116252] using wordTrace_append hprefix tailTrace_8116252
  have hstable : (prefixWord ++ tailWord_8116252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116252).length < 2 ^ (prefixWord ++ tailWord_8116252).sum := by decide
  have hdescent : baseEnd_8116252 < baseStart_8116252 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116284 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 1, 8]
def baseStart_8116284 : Nat := 118140960795 + 8116284 * 2 ^ 59
def prefixEnd_8116284 : Nat := 4983230072969 + 3 ^ 40 * 8116284 * 2
def baseEnd_8116284 : Nat := 1389184940132076078407965

theorem tailTrace_8116284 : CollatzResearch.WordTrace tailWord_8116284 prefixEnd_8116284 1389184940132076078407965 := by
  unfold tailWord_8116284
  simp only [CollatzResearch.WordTrace]
  refine ⟨148012598464048346897597953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197350131285397795863463937 148012598464048346897597953)
  ·
    refine ⟨111009448848036260173198465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148012598464048346897597953 111009448848036260173198465)
    ·
      refine ⟨83257086636027195129898849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111009448848036260173198465 83257086636027195129898849)
      ·
        refine ⟨62442814977020396347424137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83257086636027195129898849 62442814977020396347424137)
        ·
          refine ⟨46832111232765297260568103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62442814977020396347424137 46832111232765297260568103)
          ·
            refine ⟨70248166849147945890852155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46832111232765297260568103 70248166849147945890852155)
            ·
              refine ⟨105372250273721918836278233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70248166849147945890852155 105372250273721918836278233)
              ·
                refine ⟨79029187705291439127208675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105372250273721918836278233 79029187705291439127208675)
                ·
                  refine ⟨118543781557937158690813013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79029187705291439127208675 118543781557937158690813013)
                  ·
                    refine ⟨1389184940132076078407965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118543781557937158690813013 1389184940132076078407965)
                    ·
                      rfl

theorem cell23_8116284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_8116284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116284 prefixEnd_8116284 := by exact prefixLift 8116284
  have htrace : WordTrace (prefixWord ++ tailWord_8116284) baseStart_8116284 baseEnd_8116284 := by
    simpa [prefixWord, tailWord_8116284, baseEnd_8116284] using wordTrace_append hprefix tailTrace_8116284
  have hstable : (prefixWord ++ tailWord_8116284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116284).length < 2 ^ (prefixWord ++ tailWord_8116284).sum := by decide
  have hdescent : baseEnd_8116284 < baseStart_8116284 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116291 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 3, 4, 2]
def baseStart_8116291 : Nat := 118140960795 + 8116291 * 2 ^ 59
def prefixEnd_8116291 : Nat := 4983230072969 + 3 ^ 40 * 8116291 * 2
def baseEnd_8116291 : Nat := 4167558414760809707836363

theorem tailTrace_8116291 : CollatzResearch.WordTrace tailWord_8116291 prefixEnd_8116291 4167558414760809707836363 := by
  unfold tailWord_8116291
  simp only [CollatzResearch.WordTrace]
  refine ⟨296025452239071333990700727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197350301492714222660467151 296025452239071333990700727)
  ·
    refine ⟨444038178358607000986051091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296025452239071333990700727 444038178358607000986051091)
    ·
      refine ⟨666057267537910501479076637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444038178358607000986051091 666057267537910501479076637)
      ·
        refine ⟨249771475326716438054653739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 666057267537910501479076637 249771475326716438054653739)
        ·
          refine ⟨374657212990074657081980609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249771475326716438054653739 374657212990074657081980609)
          ·
            refine ⟨280992909742555992811485457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374657212990074657081980609 280992909742555992811485457)
            ·
              refine ⟨210744682306916994608614093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280992909742555992811485457 210744682306916994608614093)
              ·
                refine ⟨79029255865093872978230285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210744682306916994608614093 79029255865093872978230285)
                ·
                  refine ⟨29635970949410202366836357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79029255865093872978230285 29635970949410202366836357)
                  ·
                    refine ⟨5556744553014412943781817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29635970949410202366836357 5556744553014412943781817)
                    ·
                      refine ⟨4167558414760809707836363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5556744553014412943781817 4167558414760809707836363)
                      ·
                        rfl

theorem cell23_8116291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 4, 2].length) (baseStart_8116291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116291 prefixEnd_8116291 := by exact prefixLift 8116291
  have htrace : WordTrace (prefixWord ++ tailWord_8116291) baseStart_8116291 baseEnd_8116291 := by
    simpa [prefixWord, tailWord_8116291, baseEnd_8116291] using wordTrace_append hprefix tailTrace_8116291
  have hstable : (prefixWord ++ tailWord_8116291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116291).length < 2 ^ (prefixWord ++ tailWord_8116291).sum := by decide
  have hdescent : baseEnd_8116291 < baseStart_8116291 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116301 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_8116301 : Nat := 118140960795 + 8116301 * 2 ^ 59
def prefixEnd_8116301 : Nat := 4983230072969 + 3 ^ 40 * 8116301 * 2
def baseEnd_8116301 : Nat := 1389187849855784889570439

theorem tailTrace_8116301 : CollatzResearch.WordTrace tailWord_8116301 prefixEnd_8116301 1389187849855784889570439 := by
  unfold tailWord_8116301
  simp only [CollatzResearch.WordTrace]
  refine ⟨296025816969035105698564757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197350544646023403799043171 296025816969035105698564757)
  ·
    refine ⟨13876210170423520579620223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 296025816969035105698564757 13876210170423520579620223)
    ·
      refine ⟨20814315255635280869430335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13876210170423520579620223 20814315255635280869430335)
      ·
        refine ⟨31221472883452921304145503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20814315255635280869430335 31221472883452921304145503)
        ·
          refine ⟨46832209325179381956218255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31221472883452921304145503 46832209325179381956218255)
          ·
            refine ⟨70248313987769072934327383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46832209325179381956218255 70248313987769072934327383)
            ·
              refine ⟨105372470981653609401491075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70248313987769072934327383 105372470981653609401491075)
              ·
                refine ⟨158058706472480414102236613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105372470981653609401491075 158058706472480414102236613)
                ·
                  refine ⟨29636007463590077644169365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158058706472480414102236613 29636007463590077644169365)
                  ·
                    refine ⟨1389187849855784889570439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29636007463590077644169365 1389187849855784889570439)
                    ·
                      rfl

theorem cell23_8116301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_8116301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116301 prefixEnd_8116301 := by exact prefixLift 8116301
  have htrace : WordTrace (prefixWord ++ tailWord_8116301) baseStart_8116301 baseEnd_8116301 := by
    simpa [prefixWord, tailWord_8116301, baseEnd_8116301] using wordTrace_append hprefix tailTrace_8116301
  have hstable : (prefixWord ++ tailWord_8116301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116301).length < 2 ^ (prefixWord ++ tailWord_8116301).sum := by decide
  have hdescent : baseEnd_8116301 < baseStart_8116301 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116325 : List Nat := [1, 3, 1, 3, 2, 4, 1, 1, 1, 4, 2]
def baseStart_8116325 : Nat := 118140960795 + 8116325 * 2 ^ 59
def prefixEnd_8116325 : Nat := 4983230072969 + 3 ^ 40 * 8116325 * 2
def baseEnd_8116325 : Nat := 4167575873103062574811207

theorem tailTrace_8116325 : CollatzResearch.WordTrace tailWord_8116325 prefixEnd_8116325 4167575873103062574811207 := by
  unfold tailWord_8116325
  simp only [CollatzResearch.WordTrace]
  refine ⟨296026692320948157797438429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197351128213965438531625619 296026692320948157797438429)
  ·
    refine ⟨111010009620355559174039411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296026692320948157797438429 111010009620355559174039411)
    ·
      refine ⟨166515014430533338761059117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111010009620355559174039411 166515014430533338761059117)
      ·
        refine ⟨62443130411450002035397169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166515014430533338761059117 62443130411450002035397169)
        ·
          refine ⟨46832347808587501526547877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62443130411450002035397169 46832347808587501526547877)
          ·
            refine ⟨8781065214110156536227727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46832347808587501526547877 8781065214110156536227727)
            ·
              refine ⟨13171597821165234804341591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8781065214110156536227727 13171597821165234804341591)
              ·
                refine ⟨19757396731747852206512387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13171597821165234804341591 19757396731747852206512387)
                ·
                  refine ⟨29636095097621778309768581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19757396731747852206512387 29636095097621778309768581)
                  ·
                    refine ⟨5556767830804083433081609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29636095097621778309768581 5556767830804083433081609)
                    ·
                      refine ⟨4167575873103062574811207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5556767830804083433081609 4167575873103062574811207)
                      ·
                        rfl

theorem cell23_8116325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_8116325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116325 prefixEnd_8116325 := by exact prefixLift 8116325
  have htrace : WordTrace (prefixWord ++ tailWord_8116325) baseStart_8116325 baseEnd_8116325 := by
    simpa [prefixWord, tailWord_8116325, baseEnd_8116325] using wordTrace_append hprefix tailTrace_8116325
  have hstable : (prefixWord ++ tailWord_8116325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116325).length < 2 ^ (prefixWord ++ tailWord_8116325).sum := by decide
  have hdescent : baseEnd_8116325 < baseStart_8116325 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116348 : List Nat := [2, 2, 2, 1, 1, 4, 3, 3, 5]
def baseStart_8116348 : Nat := 118140960795 + 8116348 * 2 ^ 59
def prefixEnd_8116348 : Nat := 4983230072969 + 3 ^ 40 * 8116348 * 2
def baseEnd_8116348 : Nat := 463065298128679553869289

theorem tailTrace_8116348 : CollatzResearch.WordTrace tailWord_8116348 prefixEnd_8116348 463065298128679553869289 := by
  unfold tailWord_8116348
  simp only [CollatzResearch.WordTrace]
  refine ⟨148013765599932416362762849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197351687466576555150350465 148013765599932416362762849)
  ·
    refine ⟨111010324199949312272072137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148013765599932416362762849 111010324199949312272072137)
    ·
      refine ⟨83257743149961984204054103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111010324199949312272072137 83257743149961984204054103)
      ·
        refine ⟨124886614724942976306081155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83257743149961984204054103 124886614724942976306081155)
        ·
          refine ⟨187329922087414464459121733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124886614724942976306081155 187329922087414464459121733)
          ·
            refine ⟨35124360391390212086085325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187329922087414464459121733 35124360391390212086085325)
            ·
              refine ⟨13171635146771329532281997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35124360391390212086085325 13171635146771329532281997)
              ·
                refine ⟨4939363180039248574605749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13171635146771329532281997 4939363180039248574605749)
                ·
                  refine ⟨463065298128679553869289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4939363180039248574605749 463065298128679553869289)
                  ·
                    rfl

theorem cell23_8116348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 5].length) (baseStart_8116348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116348 prefixEnd_8116348 := by exact prefixLift 8116348
  have htrace : WordTrace (prefixWord ++ tailWord_8116348) baseStart_8116348 baseEnd_8116348 := by
    simpa [prefixWord, tailWord_8116348, baseEnd_8116348] using wordTrace_append hprefix tailTrace_8116348
  have hstable : (prefixWord ++ tailWord_8116348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116348).length < 2 ^ (prefixWord ++ tailWord_8116348).sum := by decide
  have hdescent : baseEnd_8116348 < baseStart_8116348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116361 : List Nat := [1, 2, 1, 1, 4, 2, 3, 2, 2, 5]
def baseStart_8116361 : Nat := 118140960795 + 8116361 * 2 ^ 59
def prefixEnd_8116361 : Nat := 4983230072969 + 3 ^ 40 * 8116361 * 2
def baseEnd_8116361 : Nat := 1389198119468874811320347

theorem tailTrace_8116361 : CollatzResearch.WordTrace tailWord_8116361 prefixEnd_8116361 1389198119468874811320347 := by
  unfold tailWord_8116361
  simp only [CollatzResearch.WordTrace]
  refine ⟨296028005348817735945748937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197352003565878490630499291 296028005348817735945748937)
  ·
    refine ⟨222021004011613301959311703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296028005348817735945748937 222021004011613301959311703)
    ·
      refine ⟨333031506017419952938967555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222021004011613301959311703 333031506017419952938967555)
      ·
        refine ⟨499547259026129929408451333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333031506017419952938967555 499547259026129929408451333)
        ·
          refine ⟨93665111067399361764084625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 499547259026129929408451333 93665111067399361764084625)
          ·
            refine ⟨70248833300549521323063469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93665111067399361764084625 70248833300549521323063469)
            ·
              refine ⟨26343312487706070496148801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70248833300549521323063469 26343312487706070496148801)
              ·
                refine ⟨19757484365779552872111601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26343312487706070496148801 19757484365779552872111601)
                ·
                  refine ⟨14818113274334664654083701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19757484365779552872111601 14818113274334664654083701)
                  ·
                    refine ⟨1389198119468874811320347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14818113274334664654083701 1389198119468874811320347)
                    ·
                      rfl

theorem cell23_8116361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 5].length) (baseStart_8116361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116361 prefixEnd_8116361 := by exact prefixLift 8116361
  have htrace : WordTrace (prefixWord ++ tailWord_8116361) baseStart_8116361 baseEnd_8116361 := by
    simpa [prefixWord, tailWord_8116361, baseEnd_8116361] using wordTrace_append hprefix tailTrace_8116361
  have hstable : (prefixWord ++ tailWord_8116361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116361).length < 2 ^ (prefixWord ++ tailWord_8116361).sum := by decide
  have hdescent : baseEnd_8116361 < baseStart_8116361 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116364 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 2, 2, 8]
def baseStart_8116364 : Nat := 118140960795 + 8116364 * 2 ^ 59
def prefixEnd_8116364 : Nat := 4983230072969 + 3 ^ 40 * 8116364 * 2
def baseEnd_8116364 : Nat := 4167595898848587922223527

theorem tailTrace_8116364 : CollatzResearch.WordTrace tailWord_8116364 prefixEnd_8116364 4167595898848587922223527 := by
  unfold tailWord_8116364
  simp only [CollatzResearch.WordTrace]
  refine ⟨148014057383903433729054073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197352076511871244972072097 148014057383903433729054073)
  ·
    refine ⟨111010543037927575296790555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148014057383903433729054073 111010543037927575296790555)
    ·
      refine ⟨166515814556891362945185833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111010543037927575296790555 166515814556891362945185833)
      ·
        refine ⟨124886860917668522208889375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166515814556891362945185833 124886860917668522208889375)
        ·
          refine ⟨187330291376502783313334063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124886860917668522208889375 187330291376502783313334063)
          ·
            refine ⟨280995437064754174970001095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187330291376502783313334063 280995437064754174970001095)
            ·
              refine ⟨421493155597131262455001643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280995437064754174970001095 421493155597131262455001643)
              ·
                refine ⟨632239733395696893682502465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421493155597131262455001643 632239733395696893682502465)
                ·
                  refine ⟨474179800046772670261876849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632239733395696893682502465 474179800046772670261876849)
                  ·
                    refine ⟨355634850035079502696407637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 474179800046772670261876849 355634850035079502696407637)
                    ·
                      refine ⟨4167595898848587922223527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 355634850035079502696407637 4167595898848587922223527)
                      ·
                        rfl

theorem cell23_8116364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_8116364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116364 prefixEnd_8116364 := by exact prefixLift 8116364
  have htrace : WordTrace (prefixWord ++ tailWord_8116364) baseStart_8116364 baseEnd_8116364 := by
    simpa [prefixWord, tailWord_8116364, baseEnd_8116364] using wordTrace_append hprefix tailTrace_8116364
  have hstable : (prefixWord ++ tailWord_8116364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116364).length < 2 ^ (prefixWord ++ tailWord_8116364).sum := by decide
  have hdescent : baseEnd_8116364 < baseStart_8116364 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116376 : List Nat := [2, 1, 2, 4, 4, 1, 2, 1, 2, 2, 2]
def baseStart_8116376 : Nat := 118140960795 + 8116376 * 2 ^ 59
def prefixEnd_8116376 : Nat := 4983230072969 + 3 ^ 40 * 8116376 * 2
def baseEnd_8116376 : Nat := 4167602060616441875273473

theorem tailTrace_8116376 : CollatzResearch.WordTrace tailWord_8116376 prefixEnd_8116376 4167602060616441875273473 := by
  unfold tailWord_8116376
  simp only [CollatzResearch.WordTrace]
  refine ⟨148014276221881696753772491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197352368295842262338363321 148014276221881696753772491)
  ·
    refine ⟨222021414332822545130658737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148014276221881696753772491 222021414332822545130658737)
    ·
      refine ⟨166516060749616908847994053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222021414332822545130658737 166516060749616908847994053)
      ·
        refine ⟨31221761390553170408998885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166516060749616908847994053 31221761390553170408998885)
        ·
          refine ⟨5854080260728719451687291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31221761390553170408998885 5854080260728719451687291)
          ·
            refine ⟨8781120391093079177530937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5854080260728719451687291 8781120391093079177530937)
            ·
              refine ⟨6585840293319809383148203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8781120391093079177530937 6585840293319809383148203)
              ·
                refine ⟨9878760439979714074722305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6585840293319809383148203 9878760439979714074722305)
                ·
                  refine ⟨7409070329984785556041729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9878760439979714074722305 7409070329984785556041729)
                  ·
                    refine ⟨5556802747488589167031297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7409070329984785556041729 5556802747488589167031297)
                    ·
                      refine ⟨4167602060616441875273473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5556802747488589167031297 4167602060616441875273473)
                      ·
                        rfl

theorem cell23_8116376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_8116376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116376 prefixEnd_8116376 := by exact prefixLift 8116376
  have htrace : WordTrace (prefixWord ++ tailWord_8116376) baseStart_8116376 baseEnd_8116376 := by
    simpa [prefixWord, tailWord_8116376, baseEnd_8116376] using wordTrace_append hprefix tailTrace_8116376
  have hstable : (prefixWord ++ tailWord_8116376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116376).length < 2 ^ (prefixWord ++ tailWord_8116376).sum := by decide
  have hdescent : baseEnd_8116376 < baseStart_8116376 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116421 : List Nat := [1, 3, 1, 1, 1, 1, 5, 4, 6]
def baseStart_8116421 : Nat := 118140960795 + 8116421 * 2 ^ 59
def prefixEnd_8116421 : Nat := 4983230072969 + 3 ^ 40 * 8116421 * 2
def baseEnd_8116421 : Nat := 463069463027321577690085

theorem tailTrace_8116421 : CollatzResearch.WordTrace tailWord_8116421 prefixEnd_8116421 463069463027321577690085 := by
  unfold tailWord_8116421
  simp only [CollatzResearch.WordTrace]
  refine ⟨296030193728600366192933117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197353462485733577461955411 296030193728600366192933117)
  ·
    refine ⟨111011322648225137322349919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296030193728600366192933117 111011322648225137322349919)
    ·
      refine ⟨166516983972337705983524879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111011322648225137322349919 166516983972337705983524879)
      ·
        refine ⟨249775475958506558975287319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166516983972337705983524879 249775475958506558975287319)
        ·
          refine ⟨374663213937759838462930979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249775475958506558975287319 374663213937759838462930979)
          ·
            refine ⟨561994820906639757694396469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374663213937759838462930979 561994820906639757694396469)
            ·
              refine ⟨52687014459997477283849669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 561994820906639757694396469 52687014459997477283849669)
              ·
                refine ⟨9878815211249526990721813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52687014459997477283849669 9878815211249526990721813)
                ·
                  refine ⟨463069463027321577690085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9878815211249526990721813 463069463027321577690085)
                  ·
                    rfl

theorem cell23_8116421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 6].length) (baseStart_8116421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116421 prefixEnd_8116421 := by exact prefixLift 8116421
  have htrace : WordTrace (prefixWord ++ tailWord_8116421) baseStart_8116421 baseEnd_8116421 := by
    simpa [prefixWord, tailWord_8116421, baseEnd_8116421] using wordTrace_append hprefix tailTrace_8116421
  have hstable : (prefixWord ++ tailWord_8116421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116421).length < 2 ^ (prefixWord ++ tailWord_8116421).sum := by decide
  have hdescent : baseEnd_8116421 < baseStart_8116421 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116482 : List Nat := [3, 4, 1, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_8116482 : Nat := 118140960795 + 8116482 * 2 ^ 59
def prefixEnd_8116482 : Nat := 4983230072969 + 3 ^ 40 * 8116482 * 2
def baseEnd_8116482 : Nat := 4167656489565818460547985

theorem tailTrace_8116482 : CollatzResearch.WordTrace tailWord_8116482 prefixEnd_8116482 4167656489565818460547985 := by
  unfold tailWord_8116482
  simp only [CollatzResearch.WordTrace]
  refine ⟨74008104645344843402725925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197354945720919582407269133 74008104645344843402725925)
  ·
    refine ⟨13876519621002158138011111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74008104645344843402725925 13876519621002158138011111)
    ·
      refine ⟨20814779431503237207016667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13876519621002158138011111 20814779431503237207016667)
      ·
        refine ⟨31222169147254855810525001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20814779431503237207016667 31222169147254855810525001)
        ·
          refine ⟨23416626860441141857893751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31222169147254855810525001 23416626860441141857893751)
          ·
            refine ⟨35124940290661712786840627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23416626860441141857893751 35124940290661712786840627)
            ·
              refine ⟨52687410435992569180260941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35124940290661712786840627 52687410435992569180260941)
              ·
                refine ⟨19757778913497213442597853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52687410435992569180260941 19757778913497213442597853)
                ·
                  refine ⟨7409167092561455040974195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19757778913497213442597853 7409167092561455040974195)
                  ·
                    refine ⟨11113750638842182561461293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7409167092561455040974195 11113750638842182561461293)
                    ·
                      refine ⟨4167656489565818460547985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11113750638842182561461293 4167656489565818460547985)
                      ·
                        rfl

theorem cell23_8116482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_8116482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116482 prefixEnd_8116482 := by exact prefixLift 8116482
  have htrace : WordTrace (prefixWord ++ tailWord_8116482) baseStart_8116482 baseEnd_8116482 := by
    simpa [prefixWord, tailWord_8116482, baseEnd_8116482] using wordTrace_append hprefix tailTrace_8116482
  have hstable : (prefixWord ++ tailWord_8116482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116482).length < 2 ^ (prefixWord ++ tailWord_8116482).sum := by decide
  have hdescent : baseEnd_8116482 < baseStart_8116482 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116545 : List Nat := [1, 2, 5, 2, 2, 1, 2, 8]
def baseStart_8116545 : Nat := 118140960795 + 8116545 * 2 ^ 59
def prefixEnd_8116545 : Nat := 4983230072969 + 3 ^ 40 * 8116545 * 2
def baseEnd_8116545 : Nat := 154358845883224137557785

theorem tailTrace_8116545 : CollatzResearch.WordTrace tailWord_8116545 prefixEnd_8116545 154358845883224137557785 := by
  unfold tailWord_8116545
  simp only [CollatzResearch.WordTrace]
  refine ⟨296034716380151135370447089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197356477586767423580298059 296034716380151135370447089)
  ·
    refine ⟨222026037285113351527835317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296034716380151135370447089 222026037285113351527835317)
    ·
      refine ⟨20814940995479376705734561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222026037285113351527835317 20814940995479376705734561)
      ·
        refine ⟨15611205746609532529300921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20814940995479376705734561 15611205746609532529300921)
        ·
          refine ⟨11708404309957149396975691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15611205746609532529300921 11708404309957149396975691)
          ·
            refine ⟨17562606464935724095463537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11708404309957149396975691 17562606464935724095463537)
            ·
              refine ⟨13171954848701793071597653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17562606464935724095463537 13171954848701793071597653)
              ·
                refine ⟨154358845883224137557785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13171954848701793071597653 154358845883224137557785)
                ·
                  rfl

theorem cell23_8116545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 8].length) (baseStart_8116545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116545 prefixEnd_8116545 := by exact prefixLift 8116545
  have htrace : WordTrace (prefixWord ++ tailWord_8116545) baseStart_8116545 baseEnd_8116545 := by
    simpa [prefixWord, tailWord_8116545, baseEnd_8116545] using wordTrace_append hprefix tailTrace_8116545
  have hstable : (prefixWord ++ tailWord_8116545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116545).length < 2 ^ (prefixWord ++ tailWord_8116545).sum := by decide
  have hdescent : baseEnd_8116545 < baseStart_8116545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116612 : List Nat := [2, 3, 2, 1, 1, 2, 4, 1, 1, 4, 2]
def baseStart_8116612 : Nat := 118140960795 + 8116612 * 2 ^ 59
def prefixEnd_8116612 : Nat := 4983230072969 + 3 ^ 40 * 8116612 * 2
def baseEnd_8116612 : Nat := 4167723242050902951922387

theorem tailTrace_8116612 : CollatzResearch.WordTrace tailWord_8116612 prefixEnd_8116612 4167723242050902951922387 := by
  unfold tailWord_8116612
  simp only [CollatzResearch.WordTrace]
  refine ⟨148018580035454202906568045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197358106713938937208757393 148018580035454202906568045)
  ·
    refine ⟨55506967513295326089963017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148018580035454202906568045 55506967513295326089963017)
    ·
      refine ⟨41630225634971494567472263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55506967513295326089963017 41630225634971494567472263)
      ·
        refine ⟨62445338452457241851208395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41630225634971494567472263 62445338452457241851208395)
        ·
          refine ⟨93668007678685862776812593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62445338452457241851208395 93668007678685862776812593)
          ·
            refine ⟨70251005759014397082609445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93668007678685862776812593 70251005759014397082609445)
            ·
              refine ⟨13172063579815199452989271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70251005759014397082609445 13172063579815199452989271)
              ·
                refine ⟨19758095369722799179483907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13172063579815199452989271 19758095369722799179483907)
                ·
                  refine ⟨29637143054584198769225861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19758095369722799179483907 29637143054584198769225861)
                  ·
                    refine ⟨5556964322734537269229849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29637143054584198769225861 5556964322734537269229849)
                    ·
                      refine ⟨4167723242050902951922387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5556964322734537269229849 4167723242050902951922387)
                      ·
                        rfl

theorem cell23_8116612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_8116612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116612 prefixEnd_8116612 := by exact prefixLift 8116612
  have htrace : WordTrace (prefixWord ++ tailWord_8116612) baseStart_8116612 baseEnd_8116612 := by
    simpa [prefixWord, tailWord_8116612, baseEnd_8116612] using wordTrace_append hprefix tailTrace_8116612
  have hstable : (prefixWord ++ tailWord_8116612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116612).length < 2 ^ (prefixWord ++ tailWord_8116612).sum := by decide
  have hdescent : baseEnd_8116612 < baseStart_8116612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116658 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_8116658 : Nat := 118140960795 + 8116658 * 2 ^ 59
def prefixEnd_8116658 : Nat := 4983230072969 + 3 ^ 40 * 8116658 * 2
def baseEnd_8116658 : Nat := 4167746862161009771947175

theorem tailTrace_8116658 : CollatzResearch.WordTrace tailWord_8116658 prefixEnd_8116658 4167746862161009771947175 := by
  unfold tailWord_8116658
  simp only [CollatzResearch.WordTrace]
  refine ⟨74009709457185438917327657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197359225219161170446207085 74009709457185438917327657)
  ·
    refine ⟨55507282092889079187995743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74009709457185438917327657 55507282092889079187995743)
    ·
      refine ⟨83260923139333618781993615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55507282092889079187995743 83260923139333618781993615)
      ·
        refine ⟨124891384709000428172990423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83260923139333618781993615 124891384709000428172990423)
        ·
          refine ⟨187337077063500642259485635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124891384709000428172990423 187337077063500642259485635)
          ·
            refine ⟨281005615595250963389228453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187337077063500642259485635 281005615595250963389228453)
            ·
              refine ⟨52688552924109555635480335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281005615595250963389228453 52688552924109555635480335)
              ·
                refine ⟨79032829386164333453220503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52688552924109555635480335 79032829386164333453220503)
                ·
                  refine ⟨118549244079246500179830755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79032829386164333453220503 118549244079246500179830755)
                  ·
                    refine ⟨177823866118869750269746133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118549244079246500179830755 177823866118869750269746133)
                    ·
                      refine ⟨4167746862161009771947175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177823866118869750269746133 4167746862161009771947175)
                      ·
                        rfl

theorem cell23_8116658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_8116658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116658 prefixEnd_8116658 := by exact prefixLift 8116658
  have htrace : WordTrace (prefixWord ++ tailWord_8116658) baseStart_8116658 baseEnd_8116658 := by
    simpa [prefixWord, tailWord_8116658, baseEnd_8116658] using wordTrace_append hprefix tailTrace_8116658
  have hstable : (prefixWord ++ tailWord_8116658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116658).length < 2 ^ (prefixWord ++ tailWord_8116658).sum := by decide
  have hdescent : baseEnd_8116658 < baseStart_8116658 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116712 : List Nat := [2, 1, 4, 1, 1, 3, 3, 1, 3, 4]
def baseStart_8116712 : Nat := 118140960795 + 8116712 * 2 ^ 59
def prefixEnd_8116712 : Nat := 4983230072969 + 3 ^ 40 * 8116712 * 2
def baseEnd_8116712 : Nat := 1389258196705450853557309

theorem tailTrace_8116712 : CollatzResearch.WordTrace tailWord_8116712 prefixEnd_8116712 1389258196705450853557309 := by
  unfold tailWord_8116712
  simp only [CollatzResearch.WordTrace]
  refine ⟨148020403685273061445888195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197360538247030748594517593 148020403685273061445888195)
  ·
    refine ⟨222030605527909592168832293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148020403685273061445888195 222030605527909592168832293)
    ·
      refine ⟨41630738536483048531656055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222030605527909592168832293 41630738536483048531656055)
      ·
        refine ⟨62446107804724572797484083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41630738536483048531656055 62446107804724572797484083)
        ·
          refine ⟨93669161707086859196226125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62446107804724572797484083 93669161707086859196226125)
          ·
            refine ⟨35125935640157572198584797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93669161707086859196226125 35125935640157572198584797)
            ·
              refine ⟨13172225865059089574469299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35125935640157572198584797 13172225865059089574469299)
              ·
                refine ⟨19758338797588634361703949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13172225865059089574469299 19758338797588634361703949)
                ·
                  refine ⟨7409377049095737885638981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19758338797588634361703949 7409377049095737885638981)
                  ·
                    refine ⟨1389258196705450853557309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7409377049095737885638981 1389258196705450853557309)
                    ·
                      rfl

theorem cell23_8116712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_8116712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116712 prefixEnd_8116712 := by exact prefixLift 8116712
  have htrace : WordTrace (prefixWord ++ tailWord_8116712) baseStart_8116712 baseEnd_8116712 := by
    simpa [prefixWord, tailWord_8116712, baseEnd_8116712] using wordTrace_append hprefix tailTrace_8116712
  have hstable : (prefixWord ++ tailWord_8116712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116712).length < 2 ^ (prefixWord ++ tailWord_8116712).sum := by decide
  have hdescent : baseEnd_8116712 < baseStart_8116712 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116759 : List Nat := [1, 1, 3, 6, 1, 1, 2, 2, 6]
def baseStart_8116759 : Nat := 118140960795 + 8116759 * 2 ^ 59
def prefixEnd_8116759 : Nat := 4983230072969 + 3 ^ 40 * 8116759 * 2
def baseEnd_8116759 : Nat := 463088747078568208531579

theorem tailTrace_8116759 : CollatzResearch.WordTrace tailWord_8116759 prefixEnd_8116759 463088747078568208531579 := by
  unfold tailWord_8116759
  simp only [CollatzResearch.WordTrace]
  refine ⟨296042521601375849918737331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197361681067583899945824887 296042521601375849918737331)
  ·
    refine ⟨444063782402063774878105997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296042521601375849918737331 444063782402063774878105997)
    ·
      refine ⟨166523918400773915579289749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444063782402063774878105997 166523918400773915579289749)
      ·
        refine ⟨7805808675036277292779207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 166523918400773915579289749 7805808675036277292779207)
        ·
          refine ⟨11708713012554415939168811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7805808675036277292779207 11708713012554415939168811)
          ·
            refine ⟨17563069518831623908753217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11708713012554415939168811 17563069518831623908753217)
            ·
              refine ⟨13172302139123717931564913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17563069518831623908753217 13172302139123717931564913)
              ·
                refine ⟨9879226604342788448673685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13172302139123717931564913 9879226604342788448673685)
                ·
                  refine ⟨463088747078568208531579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9879226604342788448673685 463088747078568208531579)
                  ·
                    rfl

theorem cell23_8116759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 6].length) (baseStart_8116759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116759 prefixEnd_8116759 := by exact prefixLift 8116759
  have htrace : WordTrace (prefixWord ++ tailWord_8116759) baseStart_8116759 baseEnd_8116759 := by
    simpa [prefixWord, tailWord_8116759, baseEnd_8116759] using wordTrace_append hprefix tailTrace_8116759
  have hstable : (prefixWord ++ tailWord_8116759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116759).length < 2 ^ (prefixWord ++ tailWord_8116759).sum := by decide
  have hdescent : baseEnd_8116759 < baseStart_8116759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116785 : List Nat := [1, 2, 2, 3, 1, 1, 3, 3, 1, 6]
def baseStart_8116785 : Nat := 118140960795 + 8116785 * 2 ^ 59
def prefixEnd_8116785 : Nat := 4983230072969 + 3 ^ 40 * 8116785 * 2
def baseEnd_8116785 : Nat := 1389270691401376925019697

theorem tailTrace_8116785 : CollatzResearch.WordTrace tailWord_8116785 prefixEnd_8116785 1389270691401376925019697 := by
  unfold tailWord_8116785
  simp only [CollatzResearch.WordTrace]
  refine ⟨296043469899281656359183809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197362313266187770906122539 296043469899281656359183809)
  ·
    refine ⟨222032602424461242269387857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296043469899281656359183809 222032602424461242269387857)
    ·
      refine ⟨166524451818345931702040893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222032602424461242269387857 166524451818345931702040893)
      ·
        refine ⟨62446669431879724388265335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166524451818345931702040893 62446669431879724388265335)
        ·
          refine ⟨93670004147819586582398003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62446669431879724388265335 93670004147819586582398003)
          ·
            refine ⟨140505006221729379873597005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93670004147819586582398003 140505006221729379873597005)
            ·
              refine ⟨52689377333148517452598877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140505006221729379873597005 52689377333148517452598877)
              ·
                refine ⟨19758516499930694044724579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52689377333148517452598877 19758516499930694044724579)
                ·
                  refine ⟨29637774749896041067086869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19758516499930694044724579 29637774749896041067086869)
                  ·
                    refine ⟨1389270691401376925019697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29637774749896041067086869 1389270691401376925019697)
                    ·
                      rfl

theorem cell23_8116785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_8116785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116785 prefixEnd_8116785 := by exact prefixLift 8116785
  have htrace : WordTrace (prefixWord ++ tailWord_8116785) baseStart_8116785 baseEnd_8116785 := by
    simpa [prefixWord, tailWord_8116785, baseEnd_8116785] using wordTrace_append hprefix tailTrace_8116785
  have hstable : (prefixWord ++ tailWord_8116785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116785).length < 2 ^ (prefixWord ++ tailWord_8116785).sum := by decide
  have hdescent : baseEnd_8116785 < baseStart_8116785 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116792 : List Nat := [2, 1, 2, 1, 4, 1, 2, 4, 1, 1, 4]
def baseStart_8116792 : Nat := 118140960795 + 8116792 * 2 ^ 59
def prefixEnd_8116792 : Nat := 4983230072969 + 3 ^ 40 * 8116792 * 2
def baseEnd_8116792 : Nat := 4167815668568712247671559

theorem tailTrace_8116792 : CollatzResearch.WordTrace tailWord_8116792 prefixEnd_8116792 4167815668568712247671559 := by
  unfold tailWord_8116792
  simp only [CollatzResearch.WordTrace]
  refine ⟨148021862605128148277344315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197362483473504197703125753 148021862605128148277344315)
  ·
    refine ⟨222032793907692222416016473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148021862605128148277344315 222032793907692222416016473)
    ·
      refine ⟨166524595430769166812012355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222032793907692222416016473 166524595430769166812012355)
      ·
        refine ⟨249786893146153750218018533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166524595430769166812012355 249786893146153750218018533)
        ·
          refine ⟨46835042464903828165878475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249786893146153750218018533 46835042464903828165878475)
          ·
            refine ⟨70252563697355742248817713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46835042464903828165878475 70252563697355742248817713)
            ·
              refine ⟨52689422773016806686613285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70252563697355742248817713 52689422773016806686613285)
              ·
                refine ⟨9879266769940651253739991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52689422773016806686613285 9879266769940651253739991)
                ·
                  refine ⟨14818900154910976880609987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9879266769940651253739991 14818900154910976880609987)
                  ·
                    refine ⟨22228350232366465320914981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14818900154910976880609987 22228350232366465320914981)
                    ·
                      refine ⟨4167815668568712247671559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22228350232366465320914981 4167815668568712247671559)
                      ·
                        rfl

theorem cell23_8116792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 1, 1, 4].length) (baseStart_8116792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116792 prefixEnd_8116792 := by exact prefixLift 8116792
  have htrace : WordTrace (prefixWord ++ tailWord_8116792) baseStart_8116792 baseEnd_8116792 := by
    simpa [prefixWord, tailWord_8116792, baseEnd_8116792] using wordTrace_append hprefix tailTrace_8116792
  have hstable : (prefixWord ++ tailWord_8116792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116792).length < 2 ^ (prefixWord ++ tailWord_8116792).sum := by decide
  have hdescent : baseEnd_8116792 < baseStart_8116792 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116796 : List Nat := [2, 2, 2, 2, 3, 3, 1, 1, 2, 3, 2]
def baseStart_8116796 : Nat := 118140960795 + 8116796 * 2 ^ 59
def prefixEnd_8116796 : Nat := 4983230072969 + 3 ^ 40 * 8116796 * 2
def baseEnd_8116796 : Nat := 4167817722491330232021541

theorem tailTrace_8116796 : CollatzResearch.WordTrace tailWord_8116796 prefixEnd_8116796 4167817722491330232021541 := by
  unfold tailWord_8116796
  simp only [CollatzResearch.WordTrace]
  refine ⟨148021935551120902618917121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197362580734827870158556161 148021935551120902618917121)
  ·
    refine ⟨111016451663340676964187841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148021935551120902618917121 111016451663340676964187841)
    ·
      refine ⟨83262338747505507723140881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111016451663340676964187841 83262338747505507723140881)
      ·
        refine ⟨62446754060629130792355661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83262338747505507723140881 62446754060629130792355661)
        ·
          refine ⟨23417532772735924047133373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62446754060629130792355661 23417532772735924047133373)
          ·
            refine ⟨8781574789775971517675015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23417532772735924047133373 8781574789775971517675015)
            ·
              refine ⟨13172362184663957276512523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8781574789775971517675015 13172362184663957276512523)
              ·
                refine ⟨19758543276995935914768785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13172362184663957276512523 19758543276995935914768785)
                ·
                  refine ⟨14818907457746951936076589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19758543276995935914768785 14818907457746951936076589)
                  ·
                    refine ⟨5557090296655106976028721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14818907457746951936076589 5557090296655106976028721)
                    ·
                      refine ⟨4167817722491330232021541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5557090296655106976028721 4167817722491330232021541)
                      ·
                        rfl

theorem cell23_8116796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_8116796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116796 prefixEnd_8116796 := by exact prefixLift 8116796
  have htrace : WordTrace (prefixWord ++ tailWord_8116796) baseStart_8116796 baseEnd_8116796 := by
    simpa [prefixWord, tailWord_8116796, baseEnd_8116796] using wordTrace_append hprefix tailTrace_8116796
  have hstable : (prefixWord ++ tailWord_8116796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116796).length < 2 ^ (prefixWord ++ tailWord_8116796).sum := by decide
  have hdescent : baseEnd_8116796 < baseStart_8116796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116806 : List Nat := [6, 1, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_8116806 : Nat := 118140960795 + 8116806 * 2 ^ 59
def prefixEnd_8116806 : Nat := 4983230072969 + 3 ^ 40 * 8116806 * 2
def baseEnd_8116806 : Nat := 1389274285765958397632165

theorem tailTrace_8116806 : CollatzResearch.WordTrace tailWord_8116806 prefixEnd_8116806 1389274285765958397632165 := by
  unfold tailWord_8116806
  simp only [CollatzResearch.WordTrace]
  refine ⟨9251382369756424279553071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 197362823888137051297132181 9251382369756424279553071)
  ·
    refine ⟨13877073554634636419329607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9251382369756424279553071 13877073554634636419329607)
    ·
      refine ⟨20815610331951954628994411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13877073554634636419329607 20815610331951954628994411)
      ·
        refine ⟨31223415497927931943491617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20815610331951954628994411 31223415497927931943491617)
        ·
          refine ⟨23417561623445948957618713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31223415497927931943491617 23417561623445948957618713)
          ·
            refine ⟨17563171217584461718214035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23417561623445948957618713 17563171217584461718214035)
            ·
              refine ⟨26344756826376692577321053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17563171217584461718214035 26344756826376692577321053)
              ·
                refine ⟨9879283809891259716495395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26344756826376692577321053 9879283809891259716495395)
                ·
                  refine ⟨14818925714836889574743093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9879283809891259716495395 14818925714836889574743093)
                  ·
                    refine ⟨1389274285765958397632165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14818925714836889574743093 1389274285765958397632165)
                    ·
                      rfl

theorem cell23_8116806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_8116806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116806 prefixEnd_8116806 := by exact prefixLift 8116806
  have htrace : WordTrace (prefixWord ++ tailWord_8116806) baseStart_8116806 baseEnd_8116806 := by
    simpa [prefixWord, tailWord_8116806, baseEnd_8116806] using wordTrace_append hprefix tailTrace_8116806
  have hstable : (prefixWord ++ tailWord_8116806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116806).length < 2 ^ (prefixWord ++ tailWord_8116806).sum := by decide
  have hdescent : baseEnd_8116806 < baseStart_8116806 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116825 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 2, 7, 3]
def baseStart_8116825 : Nat := 118140960795 + 8116825 * 2 ^ 59
def prefixEnd_8116825 : Nat := 4983230072969 + 3 ^ 40 * 8116825 * 2
def baseEnd_8116825 : Nat := 4167832613430310618558907

theorem tailTrace_8116825 : CollatzResearch.WordTrace tailWord_8116825 prefixEnd_8116825 4167832613430310618558907 := by
  unfold tailWord_8116825
  simp only [CollatzResearch.WordTrace]
  refine ⟨296044928819136743190639929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197363285879424495460426619 296044928819136743190639929)
  ·
    refine ⟨222033696614352557392979947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296044928819136743190639929 222033696614352557392979947)
    ·
      refine ⟨333050544921528836089469921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222033696614352557392979947 333050544921528836089469921)
      ·
        refine ⟨249787908691146627067102441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333050544921528836089469921 249787908691146627067102441)
        ·
          refine ⟨187340931518359970300326831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249787908691146627067102441 187340931518359970300326831)
          ·
            refine ⟨281011397277539955450490247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187340931518359970300326831 281011397277539955450490247)
            ·
              refine ⟨421517095916309933175735371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281011397277539955450490247 421517095916309933175735371)
              ·
                refine ⟨632275643874464899763603057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421517095916309933175735371 632275643874464899763603057)
                ·
                  refine ⟨474206732905848674822702293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632275643874464899763603057 474206732905848674822702293)
                  ·
                    refine ⟨11114220302480828316157085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 474206732905848674822702293 11114220302480828316157085)
                    ·
                      refine ⟨4167832613430310618558907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11114220302480828316157085 4167832613430310618558907)
                      ·
                        rfl

theorem cell23_8116825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_8116825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116825 prefixEnd_8116825 := by exact prefixLift 8116825
  have htrace : WordTrace (prefixWord ++ tailWord_8116825) baseStart_8116825 baseEnd_8116825 := by
    simpa [prefixWord, tailWord_8116825, baseEnd_8116825] using wordTrace_append hprefix tailTrace_8116825
  have hstable : (prefixWord ++ tailWord_8116825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116825).length < 2 ^ (prefixWord ++ tailWord_8116825).sum := by decide
  have hdescent : baseEnd_8116825 < baseStart_8116825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116846 : List Nat := [4, 1, 2, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_8116846 : Nat := 118140960795 + 8116846 * 2 ^ 59
def prefixEnd_8116846 : Nat := 4983230072969 + 3 ^ 40 * 8116846 * 2
def baseEnd_8116846 : Nat := 4167843396524055036396311

theorem tailTrace_8116846 : CollatzResearch.WordTrace tailWord_8116846 prefixEnd_8116846 4167843396524055036396311 := by
  unfold tailWord_8116846
  simp only [CollatzResearch.WordTrace]
  refine ⟨37005711844007582972144299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197363796501373775851436261 37005711844007582972144299)
  ·
    refine ⟨55508567766011374458216449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37005711844007582972144299 55508567766011374458216449)
    ·
      refine ⟨41631425824508530843662337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55508567766011374458216449 41631425824508530843662337)
      ·
        refine ⟨31223569368381398132746753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41631425824508530843662337 31223569368381398132746753)
        ·
          refine ⟨23417677026286048599560065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31223569368381398132746753 23417677026286048599560065)
          ·
            refine ⟨17563257769714536449670049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23417677026286048599560065 17563257769714536449670049)
            ·
              refine ⟨13172443327285902337252537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17563257769714536449670049 13172443327285902337252537)
              ·
                refine ⟨9879332495464426752939403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13172443327285902337252537 9879332495464426752939403)
                ·
                  refine ⟨14818998743196640129409105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9879332495464426752939403 14818998743196640129409105)
                  ·
                    refine ⟨11114249057397480097056829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14818998743196640129409105 11114249057397480097056829)
                    ·
                      refine ⟨4167843396524055036396311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11114249057397480097056829 4167843396524055036396311)
                      ·
                        rfl

theorem cell23_8116846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_8116846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116846 prefixEnd_8116846 := by exact prefixLift 8116846
  have htrace : WordTrace (prefixWord ++ tailWord_8116846) baseStart_8116846 baseEnd_8116846 := by
    simpa [prefixWord, tailWord_8116846, baseEnd_8116846] using wordTrace_append hprefix tailTrace_8116846
  have hstable : (prefixWord ++ tailWord_8116846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116846).length < 2 ^ (prefixWord ++ tailWord_8116846).sum := by decide
  have hdescent : baseEnd_8116846 < baseStart_8116846 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116855 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 5]
def baseStart_8116855 : Nat := 118140960795 + 8116855 * 2 ^ 59
def prefixEnd_8116855 : Nat := 4983230072969 + 3 ^ 40 * 8116855 * 2
def baseEnd_8116855 : Nat := 4167848017849945501183769

theorem tailTrace_8116855 : CollatzResearch.WordTrace tailWord_8116855 prefixEnd_8116855 4167848017849945501183769 := by
  unfold tailWord_8116855
  simp only [CollatzResearch.WordTrace]
  refine ⟨296046023009028058314232019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197364015339352038876154679 296046023009028058314232019)
  ·
    refine ⟨444069034513542087471348029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296046023009028058314232019 444069034513542087471348029)
    ·
      refine ⟨166525887942578282801755511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444069034513542087471348029 166525887942578282801755511)
      ·
        refine ⟨249788831913867424202633267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166525887942578282801755511 249788831913867424202633267)
        ·
          refine ⟨374683247870801136303949901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249788831913867424202633267 374683247870801136303949901)
          ·
            refine ⟨140506217951550426113981213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374683247870801136303949901 140506217951550426113981213)
            ·
              refine ⟨52689831731831409792742955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140506217951550426113981213 52689831731831409792742955)
              ·
                refine ⟨79034747597747114689114433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52689831731831409792742955 79034747597747114689114433)
                ·
                  refine ⟨59276060698310336016835825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79034747597747114689114433 59276060698310336016835825)
                  ·
                    refine ⟨44457045523732752012626869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59276060698310336016835825 44457045523732752012626869)
                    ·
                      refine ⟨4167848017849945501183769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44457045523732752012626869 4167848017849945501183769)
                      ·
                        rfl

theorem cell23_8116855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_8116855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116855 prefixEnd_8116855 := by exact prefixLift 8116855
  have htrace : WordTrace (prefixWord ++ tailWord_8116855) baseStart_8116855 baseEnd_8116855 := by
    simpa [prefixWord, tailWord_8116855, baseEnd_8116855] using wordTrace_append hprefix tailTrace_8116855
  have hstable : (prefixWord ++ tailWord_8116855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116855).length < 2 ^ (prefixWord ++ tailWord_8116855).sum := by decide
  have hdescent : baseEnd_8116855 < baseStart_8116855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116875 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 2, 6]
def baseStart_8116875 : Nat := 118140960795 + 8116875 * 2 ^ 59
def prefixEnd_8116875 : Nat := 4983230072969 + 3 ^ 40 * 8116875 * 2
def baseEnd_8116875 : Nat := 1389286095821011807644559

theorem tailTrace_8116875 : CollatzResearch.WordTrace tailWord_8116875 prefixEnd_8116875 1389286095821011807644559 := by
  unfold tailWord_8116875
  simp only [CollatzResearch.WordTrace]
  refine ⟨296046752468955601729960079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197364501645970401153306719 296046752468955601729960079)
  ·
    refine ⟨444070128703433402594940119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296046752468955601729960079 444070128703433402594940119)
    ·
      refine ⟨666105193055150103892410179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444070128703433402594940119 666105193055150103892410179)
      ·
        refine ⟨999157789582725155838615269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666105193055150103892410179 999157789582725155838615269)
        ·
          refine ⟨187342085546760966719740363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 999157789582725155838615269 187342085546760966719740363)
          ·
            refine ⟨281013128320141450079610545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187342085546760966719740363 281013128320141450079610545)
            ·
              refine ⟨210759846240106087559707909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281013128320141450079610545 210759846240106087559707909)
              ·
                refine ⟨39517471170019891417445233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210759846240106087559707909 39517471170019891417445233)
                ·
                  refine ⟨29638103377514918563083925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39517471170019891417445233 29638103377514918563083925)
                  ·
                    refine ⟨1389286095821011807644559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29638103377514918563083925 1389286095821011807644559)
                    ·
                      rfl

theorem cell23_8116875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 6].length) (baseStart_8116875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116875 prefixEnd_8116875 := by exact prefixLift 8116875
  have htrace : WordTrace (prefixWord ++ tailWord_8116875) baseStart_8116875 baseEnd_8116875 := by
    simpa [prefixWord, tailWord_8116875, baseEnd_8116875] using wordTrace_append hprefix tailTrace_8116875
  have hstable : (prefixWord ++ tailWord_8116875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116875).length < 2 ^ (prefixWord ++ tailWord_8116875).sum := by decide
  have hdescent : baseEnd_8116875 < baseStart_8116875 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116899 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 6, 2, 2]
def baseStart_8116899 : Nat := 118140960795 + 8116899 * 2 ^ 59
def prefixEnd_8116899 : Nat := 4983230072969 + 3 ^ 40 * 8116899 * 2
def baseEnd_8116899 : Nat := 4167870610998743329033567

theorem tailTrace_8116899 : CollatzResearch.WordTrace tailWord_8116899 prefixEnd_8116899 4167870610998743329033567 := by
  unfold tailWord_8116899
  simp only [CollatzResearch.WordTrace]
  refine ⟨296047627820868653828833751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197365085213912435885889167 296047627820868653828833751)
  ·
    refine ⟨444071441731302980743250627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296047627820868653828833751 444071441731302980743250627)
    ·
      refine ⟨666107162596954471114875941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444071441731302980743250627 666107162596954471114875941)
      ·
        refine ⟨124895092986928963334039239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 666107162596954471114875941 124895092986928963334039239)
        ·
          refine ⟨187342639480393445001058859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124895092986928963334039239 187342639480393445001058859)
          ·
            refine ⟨281013959220590167501588289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187342639480393445001058859 281013959220590167501588289)
            ·
              refine ⟨210760469415442625626191217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281013959220590167501588289 210760469415442625626191217)
              ·
                refine ⟨158070352061581969219643413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210760469415442625626191217 158070352061581969219643413)
                ·
                  refine ⟨7409547752886654807170785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158070352061581969219643413 7409547752886654807170785)
                  ·
                    refine ⟨5557160814664991105378089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7409547752886654807170785 5557160814664991105378089)
                    ·
                      refine ⟨4167870610998743329033567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5557160814664991105378089 4167870610998743329033567)
                      ·
                        rfl

theorem cell23_8116899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_8116899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116899 prefixEnd_8116899 := by exact prefixLift 8116899
  have htrace : WordTrace (prefixWord ++ tailWord_8116899) baseStart_8116899 baseEnd_8116899 := by
    simpa [prefixWord, tailWord_8116899, baseEnd_8116899] using wordTrace_append hprefix tailTrace_8116899
  have hstable : (prefixWord ++ tailWord_8116899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116899).length < 2 ^ (prefixWord ++ tailWord_8116899).sum := by decide
  have hdescent : baseEnd_8116899 < baseStart_8116899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116903 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_8116903 : Nat := 118140960795 + 8116903 * 2 ^ 59
def prefixEnd_8116903 : Nat := 4983230072969 + 3 ^ 40 * 8116903 * 2
def baseEnd_8116903 : Nat := 4167872664921361313383549

theorem tailTrace_8116903 : CollatzResearch.WordTrace tailWord_8116903 prefixEnd_8116903 4167872664921361313383549 := by
  unfold tailWord_8116903
  simp only [CollatzResearch.WordTrace]
  refine ⟨296047773712854162511979363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197365182475236108341319575 296047773712854162511979363)
  ·
    refine ⟨444071660569281243767969045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296047773712854162511979363 444071660569281243767969045)
    ·
      refine ⟨20815859089185058301623549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 444071660569281243767969045 20815859089185058301623549)
      ·
        refine ⟨7805947158444396863108831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20815859089185058301623549 7805947158444396863108831)
        ·
          refine ⟨11708920737666595294663247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7805947158444396863108831 11708920737666595294663247)
          ·
            refine ⟨17563381106499892941994871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11708920737666595294663247 17563381106499892941994871)
            ·
              refine ⟨26345071659749839412992307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17563381106499892941994871 26345071659749839412992307)
              ·
                refine ⟨39517607489624759119488461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26345071659749839412992307 39517607489624759119488461)
                ·
                  refine ⟨14819102808609284669808173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39517607489624759119488461 14819102808609284669808173)
                  ·
                    refine ⟨5557163553228481751178065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14819102808609284669808173 5557163553228481751178065)
                    ·
                      refine ⟨4167872664921361313383549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5557163553228481751178065 4167872664921361313383549)
                      ·
                        rfl

theorem cell23_8116903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_8116903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116903 prefixEnd_8116903 := by exact prefixLift 8116903
  have htrace : WordTrace (prefixWord ++ tailWord_8116903) baseStart_8116903 baseEnd_8116903 := by
    simpa [prefixWord, tailWord_8116903, baseEnd_8116903] using wordTrace_append hprefix tailTrace_8116903
  have hstable : (prefixWord ++ tailWord_8116903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116903).length < 2 ^ (prefixWord ++ tailWord_8116903).sum := by decide
  have hdescent : baseEnd_8116903 < baseStart_8116903 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116989 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 4, 4, 2]
def baseStart_8116989 : Nat := 118140960795 + 8116989 * 2 ^ 59
def prefixEnd_8116989 : Nat := 4983230072969 + 3 ^ 40 * 8116989 * 2
def baseEnd_8116989 : Nat := 4167916824257647976908153

theorem tailTrace_8116989 : CollatzResearch.WordTrace tailWord_8116989 prefixEnd_8116989 4167916824257647976908153 := by
  unfold tailWord_8116989
  simp only [CollatzResearch.WordTrace]
  refine ⟨296050910390542599199610021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197367273593695066133073347 296050910390542599199610021)
  ·
    refine ⟨55509545698226737349926879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296050910390542599199610021 55509545698226737349926879)
    ·
      refine ⟨83264318547340106024890319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55509545698226737349926879 83264318547340106024890319)
      ·
        refine ⟨124896477821010159037335479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83264318547340106024890319 124896477821010159037335479)
        ·
          refine ⟨187344716731515238556003219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124896477821010159037335479 187344716731515238556003219)
          ·
            refine ⟨281017075097272857834004829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187344716731515238556003219 281017075097272857834004829)
            ·
              refine ⟨105381403161477321687751811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281017075097272857834004829 105381403161477321687751811)
              ·
                refine ⟨158072104742215982531627717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105381403161477321687751811 158072104742215982531627717)
                ·
                  refine ⟨29638519639165496724680197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158072104742215982531627717 29638519639165496724680197)
                  ·
                    refine ⟨5557222432343530635877537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29638519639165496724680197 5557222432343530635877537)
                    ·
                      refine ⟨4167916824257647976908153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5557222432343530635877537 4167916824257647976908153)
                      ·
                        rfl

theorem cell23_8116989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_8116989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116989 prefixEnd_8116989 := by exact prefixLift 8116989
  have htrace : WordTrace (prefixWord ++ tailWord_8116989) baseStart_8116989 baseEnd_8116989 := by
    simpa [prefixWord, tailWord_8116989, baseEnd_8116989] using wordTrace_append hprefix tailTrace_8116989
  have hstable : (prefixWord ++ tailWord_8116989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116989).length < 2 ^ (prefixWord ++ tailWord_8116989).sum := by decide
  have hdescent : baseEnd_8116989 < baseStart_8116989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8116992 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 3]
def baseStart_8116992 : Nat := 118140960795 + 8116992 * 2 ^ 59
def prefixEnd_8116992 : Nat := 4983230072969 + 3 ^ 40 * 8116992 * 2
def baseEnd_8116992 : Nat := 4167918364699611465170639

theorem tailTrace_8116992 : CollatzResearch.WordTrace tailWord_8116992 prefixEnd_8116992 4167918364699611465170639 := by
  unfold tailWord_8116992
  simp only [CollatzResearch.WordTrace]
  refine ⟨148025509904765865355984615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197367346539687820474646153 148025509904765865355984615)
  ·
    refine ⟨222038264857148798033976923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148025509904765865355984615 222038264857148798033976923)
    ·
      refine ⟨333057397285723197050965385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222038264857148798033976923 333057397285723197050965385)
      ·
        refine ⟨249793047964292397788224039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333057397285723197050965385 249793047964292397788224039)
        ·
          refine ⟨374689571946438596682336059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249793047964292397788224039 374689571946438596682336059)
          ·
            refine ⟨562034357919657895023504089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374689571946438596682336059 562034357919657895023504089)
            ·
              refine ⟨421525768439743421267628067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562034357919657895023504089 421525768439743421267628067)
              ·
                refine ⟨632288652659615131901442101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421525768439743421267628067 632288652659615131901442101)
                ·
                  refine ⟨59277061186838918615760197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 632288652659615131901442101 59277061186838918615760197)
                  ·
                    refine ⟨11114448972532297240455037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59277061186838918615760197 11114448972532297240455037)
                    ·
                      refine ⟨4167918364699611465170639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11114448972532297240455037 4167918364699611465170639)
                      ·
                        rfl

theorem cell23_8116992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_8116992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8116992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8116992 prefixEnd_8116992 := by exact prefixLift 8116992
  have htrace : WordTrace (prefixWord ++ tailWord_8116992) baseStart_8116992 baseEnd_8116992 := by
    simpa [prefixWord, tailWord_8116992, baseEnd_8116992] using wordTrace_append hprefix tailTrace_8116992
  have hstable : (prefixWord ++ tailWord_8116992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8116992).length < 2 ^ (prefixWord ++ tailWord_8116992).sum := by decide
  have hdescent : baseEnd_8116992 < baseStart_8116992 := by decide
  rcases family_descends (prefixWord ++ tailWord_8116992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117002 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_8117002 : Nat := 118140960795 + 8117002 * 2 ^ 59
def prefixEnd_8117002 : Nat := 4983230072969 + 3 ^ 40 * 8117002 * 2
def baseEnd_8117002 : Nat := 4167923499506156426045593

theorem tailTrace_8117002 : CollatzResearch.WordTrace tailWord_8117002 prefixEnd_8117002 4167923499506156426045593 := by
  unfold tailWord_8117002
  simp only [CollatzResearch.WordTrace]
  refine ⟨74012846134873875604958315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197367589692997001613222173 74012846134873875604958315)
  ·
    refine ⟨111019269202310813407437473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74012846134873875604958315 111019269202310813407437473)
    ·
      refine ⟨83264451901733110055578105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111019269202310813407437473 83264451901733110055578105)
      ·
        refine ⟨62448338926299832541683579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83264451901733110055578105 62448338926299832541683579)
        ·
          refine ⟨93672508389449748812525369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62448338926299832541683579 93672508389449748812525369)
          ·
            refine ⟨70254381292087311609394027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93672508389449748812525369 70254381292087311609394027)
            ·
              refine ⟨105381571938130967414091041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70254381292087311609394027 105381571938130967414091041)
              ·
                refine ⟨79036178953598225560568281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105381571938130967414091041 79036178953598225560568281)
                ·
                  refine ⟨59277134215198669170426211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79036178953598225560568281 59277134215198669170426211)
                  ·
                    refine ⟨88915701322798003755639317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59277134215198669170426211 88915701322798003755639317)
                    ·
                      refine ⟨4167923499506156426045593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88915701322798003755639317 4167923499506156426045593)
                      ·
                        rfl

theorem cell23_8117002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_8117002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117002 prefixEnd_8117002 := by exact prefixLift 8117002
  have htrace : WordTrace (prefixWord ++ tailWord_8117002) baseStart_8117002 baseEnd_8117002 := by
    simpa [prefixWord, tailWord_8117002, baseEnd_8117002] using wordTrace_append hprefix tailTrace_8117002
  have hstable : (prefixWord ++ tailWord_8117002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117002).length < 2 ^ (prefixWord ++ tailWord_8117002).sum := by decide
  have hdescent : baseEnd_8117002 < baseStart_8117002 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117050 : List Nat := [3, 1, 1, 1, 6, 1, 3, 2, 1, 4]
def baseStart_8117050 : Nat := 118140960795 + 8117050 * 2 ^ 59
def prefixEnd_8117050 : Nat := 4983230072969 + 3 ^ 40 * 8117050 * 2
def baseEnd_8117050 : Nat := 1389316048859190746081791

theorem tailTrace_8117050 : CollatzResearch.WordTrace tailWord_8117050 prefixEnd_8117050 1389316048859190746081791 := by
  unfold tailWord_8117050
  simp only [CollatzResearch.WordTrace]
  refine ⟨74013283810830401654395151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197368756828881071078387069 74013283810830401654395151)
  ·
    refine ⟨111019925716245602481592727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74013283810830401654395151 111019925716245602481592727)
    ·
      refine ⟨166529888574368403722389091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111019925716245602481592727 166529888574368403722389091)
      ·
        refine ⟨249794832861552605583583637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166529888574368403722389091 249794832861552605583583637)
        ·
          refine ⟨11709132790385278386730483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 249794832861552605583583637 11709132790385278386730483)
          ·
            refine ⟨17563699185577917580095725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11709132790385278386730483 17563699185577917580095725)
            ·
              refine ⟨6586387194591719092535897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17563699185577917580095725 6586387194591719092535897)
              ·
                refine ⟨4939790395943789319401923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6586387194591719092535897 4939790395943789319401923)
                ·
                  refine ⟨7409685593915683979102885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4939790395943789319401923 7409685593915683979102885)
                  ·
                    refine ⟨1389316048859190746081791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7409685593915683979102885 1389316048859190746081791)
                    ·
                      rfl

theorem cell23_8117050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 1, 4].length) (baseStart_8117050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117050 prefixEnd_8117050 := by exact prefixLift 8117050
  have htrace : WordTrace (prefixWord ++ tailWord_8117050) baseStart_8117050 baseEnd_8117050 := by
    simpa [prefixWord, tailWord_8117050, baseEnd_8117050] using wordTrace_append hprefix tailTrace_8117050
  have hstable : (prefixWord ++ tailWord_8117050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117050).length < 2 ^ (prefixWord ++ tailWord_8117050).sum := by decide
  have hdescent : baseEnd_8117050 < baseStart_8117050 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117052 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_8117052 : Nat := 118140960795 + 8117052 * 2 ^ 59
def prefixEnd_8117052 : Nat := 4983230072969 + 3 ^ 40 * 8117052 * 2
def baseEnd_8117052 : Nat := 4167949173538881230420363

theorem tailTrace_8117052 : CollatzResearch.WordTrace tailWord_8117052 prefixEnd_8117052 4167949173538881230420363 := by
  unfold tailWord_8117052
  simp only [CollatzResearch.WordTrace]
  refine ⟨148026604094657180479576705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197368805459542907306102273 148026604094657180479576705)
  ·
    refine ⟨111019953070992885359682529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148026604094657180479576705 111019953070992885359682529)
    ·
      refine ⟨83264964803244664019761897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111019953070992885359682529 83264964803244664019761897)
      ·
        refine ⟨62448723602433498014821423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83264964803244664019761897 62448723602433498014821423)
        ·
          refine ⟨93673085403650247022232135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62448723602433498014821423 93673085403650247022232135)
          ·
            refine ⟨140509628105475370533348203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93673085403650247022232135 140509628105475370533348203)
            ·
              refine ⟨210764442158213055800022305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140509628105475370533348203 210764442158213055800022305)
              ·
                refine ⟨158073331618659791850016729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210764442158213055800022305 158073331618659791850016729)
                ·
                  refine ⟨118554998713994843887512547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158073331618659791850016729 118554998713994843887512547)
                  ·
                    refine ⟨177832498070992265831268821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118554998713994843887512547 177832498070992265831268821)
                    ·
                      refine ⟨4167949173538881230420363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177832498070992265831268821 4167949173538881230420363)
                      ·
                        rfl

theorem cell23_8117052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_8117052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117052 prefixEnd_8117052 := by exact prefixLift 8117052
  have htrace : WordTrace (prefixWord ++ tailWord_8117052) baseStart_8117052 baseEnd_8117052 := by
    simpa [prefixWord, tailWord_8117052, baseEnd_8117052] using wordTrace_append hprefix tailTrace_8117052
  have hstable : (prefixWord ++ tailWord_8117052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117052).length < 2 ^ (prefixWord ++ tailWord_8117052).sum := by decide
  have hdescent : baseEnd_8117052 < baseStart_8117052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117076 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_8117076 : Nat := 118140960795 + 8117076 * 2 ^ 59
def prefixEnd_8117076 : Nat := 4983230072969 + 3 ^ 40 * 8117076 * 2
def baseEnd_8117076 : Nat := 1389320499024863045506751

theorem tailTrace_8117076 : CollatzResearch.WordTrace tailWord_8117076 prefixEnd_8117076 1389320499024863045506751 := by
  unfold tailWord_8117076
  simp only [CollatzResearch.WordTrace]
  refine ⟨148027041770613706529013541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197369389027484942038684721 148027041770613706529013541)
  ·
    refine ⟨27755070331990069974190039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148027041770613706529013541 27755070331990069974190039)
    ·
      refine ⟨41632605497985104961285059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27755070331990069974190039 41632605497985104961285059)
      ·
        refine ⟨62448908246977657441927589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41632605497985104961285059 62448908246977657441927589)
        ·
          refine ⟨11709170296308310770361423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62448908246977657441927589 11709170296308310770361423)
          ·
            refine ⟨17563755444462466155542135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11709170296308310770361423 17563755444462466155542135)
            ·
              refine ⟨26345633166693699233313203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17563755444462466155542135 26345633166693699233313203)
              ·
                refine ⟨39518449750040548849969805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26345633166693699233313203 39518449750040548849969805)
                ·
                  refine ⟨14819418656265205818738677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39518449750040548849969805 14819418656265205818738677)
                  ·
                    refine ⟨1389320499024863045506751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14819418656265205818738677 1389320499024863045506751)
                    ·
                      rfl

theorem cell23_8117076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_8117076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117076 prefixEnd_8117076 := by exact prefixLift 8117076
  have htrace : WordTrace (prefixWord ++ tailWord_8117076) baseStart_8117076 baseEnd_8117076 := by
    simpa [prefixWord, tailWord_8117076, baseEnd_8117076] using wordTrace_append hprefix tailTrace_8117076
  have hstable : (prefixWord ++ tailWord_8117076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117076).length < 2 ^ (prefixWord ++ tailWord_8117076).sum := by decide
  have hdescent : baseEnd_8117076 < baseStart_8117076 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117089 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 4, 4]
def baseStart_8117089 : Nat := 118140960795 + 8117089 * 2 ^ 59
def prefixEnd_8117089 : Nat := 4983230072969 + 3 ^ 40 * 8117089 * 2
def baseEnd_8117089 : Nat := 1389322724107699195219231

theorem tailTrace_8117089 : CollatzResearch.WordTrace tailWord_8117089 prefixEnd_8117089 1389322724107699195219231 := by
  unfold tailWord_8117089
  simp only [CollatzResearch.WordTrace]
  refine ⟨296054557690180316278250321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197369705126786877518833547 296054557690180316278250321)
  ·
    refine ⟨222040918267635237208687741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296054557690180316278250321 222040918267635237208687741)
    ·
      refine ⟨83265344350363213953257903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222040918267635237208687741 83265344350363213953257903)
      ·
        refine ⟨124898016525544820929886855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83265344350363213953257903 124898016525544820929886855)
        ·
          refine ⟨187347024788317231394830283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124898016525544820929886855 187347024788317231394830283)
          ·
            refine ⟨281020537182475847092245425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187347024788317231394830283 281020537182475847092245425)
            ·
              refine ⟨210765402886856885319184069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281020537182475847092245425 210765402886856885319184069)
              ·
                refine ⟨39518513041285665997347013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210765402886856885319184069 39518513041285665997347013)
                ·
                  refine ⟨7409721195241062374502565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39518513041285665997347013 7409721195241062374502565)
                  ·
                    refine ⟨1389322724107699195219231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7409721195241062374502565 1389322724107699195219231)
                    ·
                      rfl

theorem cell23_8117089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_8117089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117089 prefixEnd_8117089 := by exact prefixLift 8117089
  have htrace : WordTrace (prefixWord ++ tailWord_8117089) baseStart_8117089 baseEnd_8117089 := by
    simpa [prefixWord, tailWord_8117089, baseEnd_8117089] using wordTrace_append hprefix tailTrace_8117089
  have hstable : (prefixWord ++ tailWord_8117089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117089).length < 2 ^ (prefixWord ++ tailWord_8117089).sum := by decide
  have hdescent : baseEnd_8117089 < baseStart_8117089 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117099 : List Nat := [1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 5]
def baseStart_8117099 : Nat := 118140960795 + 8117099 * 2 ^ 59
def prefixEnd_8117099 : Nat := 4983230072969 + 3 ^ 40 * 8117099 * 2
def baseEnd_8117099 : Nat := 4167973307129642546532647

theorem tailTrace_8117099 : CollatzResearch.WordTrace tailWord_8117099 prefixEnd_8117099 4167973307129642546532647 := by
  unfold tailWord_8117099
  simp only [CollatzResearch.WordTrace]
  refine ⟨296054922420144087986114351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197369948280096058657409567 296054922420144087986114351)
  ·
    refine ⟨444082383630216131979171527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296054922420144087986114351 444082383630216131979171527)
    ·
      refine ⟨666123575445324197968757291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444082383630216131979171527 666123575445324197968757291)
      ·
        refine ⟨999185363167986296953135937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666123575445324197968757291 999185363167986296953135937)
        ·
          refine ⟨749389022375989722714851953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 999185363167986296953135937 749389022375989722714851953)
          ·
            refine ⟨562041766781992292036138965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 749389022375989722714851953 562041766781992292036138965)
            ·
              refine ⟨13172853908952944344597007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 562041766781992292036138965 13172853908952944344597007)
              ·
                refine ⟨19759280863429416516895511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13172853908952944344597007 19759280863429416516895511)
                ·
                  refine ⟨29638921295144124775343267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19759280863429416516895511 29638921295144124775343267)
                  ·
                    refine ⟨44458381942716187163014901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29638921295144124775343267 44458381942716187163014901)
                    ·
                      refine ⟨4167973307129642546532647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44458381942716187163014901 4167973307129642546532647)
                      ·
                        rfl

theorem cell23_8117099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 5].length) (baseStart_8117099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117099 prefixEnd_8117099 := by exact prefixLift 8117099
  have htrace : WordTrace (prefixWord ++ tailWord_8117099) baseStart_8117099 baseEnd_8117099 := by
    simpa [prefixWord, tailWord_8117099, baseEnd_8117099] using wordTrace_append hprefix tailTrace_8117099
  have hstable : (prefixWord ++ tailWord_8117099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117099).length < 2 ^ (prefixWord ++ tailWord_8117099).sum := by decide
  have hdescent : baseEnd_8117099 < baseStart_8117099 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117106 : List Nat := [3, 2, 1, 2, 1, 1, 3, 4, 2, 4]
def baseStart_8117106 : Nat := 118140960795 + 8117106 * 2 ^ 59
def prefixEnd_8117106 : Nat := 4983230072969 + 3 ^ 40 * 8117106 * 2
def baseEnd_8117106 : Nat := 1389325633831408006381705

theorem tailTrace_8117106 : CollatzResearch.WordTrace tailWord_8117106 prefixEnd_8117106 1389325633831408006381705 := by
  unfold tailWord_8117106
  simp only [CollatzResearch.WordTrace]
  refine ⟨74013794432779682045404793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197370118487412485454412781 74013794432779682045404793)
  ·
    refine ⟨55510345824584761534053595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74013794432779682045404793 55510345824584761534053595)
    ·
      refine ⟨83265518736877142301080393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55510345824584761534053595 83265518736877142301080393)
      ·
        refine ⟨62449139052657856725810295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83265518736877142301080393 62449139052657856725810295)
        ·
          refine ⟨93673708578986785088715443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62449139052657856725810295 93673708578986785088715443)
          ·
            refine ⟨140510562868480177633073165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93673708578986785088715443 140510562868480177633073165)
            ·
              refine ⟨52691461075680066612402437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140510562868480177633073165 52691461075680066612402437)
              ·
                refine ⟨9879648951690012489825457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52691461075680066612402437 9879648951690012489825457)
                ·
                  refine ⟨7409736713767509367369093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9879648951690012489825457 7409736713767509367369093)
                  ·
                    refine ⟨1389325633831408006381705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7409736713767509367369093 1389325633831408006381705)
                    ·
                      rfl

theorem cell23_8117106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_8117106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117106 prefixEnd_8117106 := by exact prefixLift 8117106
  have htrace : WordTrace (prefixWord ++ tailWord_8117106) baseStart_8117106 baseEnd_8117106 := by
    simpa [prefixWord, tailWord_8117106, baseEnd_8117106] using wordTrace_append hprefix tailTrace_8117106
  have hstable : (prefixWord ++ tailWord_8117106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117106).length < 2 ^ (prefixWord ++ tailWord_8117106).sum := by decide
  have hdescent : baseEnd_8117106 < baseStart_8117106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117112 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 2, 2, 7]
def baseStart_8117112 : Nat := 118140960795 + 8117112 * 2 ^ 59
def prefixEnd_8117112 : Nat := 4983230072969 + 3 ^ 40 * 8117112 * 2
def baseEnd_8117112 : Nat := 4167979982378150995670087

theorem tailTrace_8117112 : CollatzResearch.WordTrace tailWord_8117112 prefixEnd_8117112 4167979982378150995670087 := by
  unfold tailWord_8117112
  simp only [CollatzResearch.WordTrace]
  refine ⟨148027698284548495603168795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197370264379397994137558393 148027698284548495603168795)
  ·
    refine ⟨222041547426822743404753193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148027698284548495603168795 222041547426822743404753193)
    ·
      refine ⟨166531160570117057553564895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222041547426822743404753193 166531160570117057553564895)
      ·
        refine ⟨249796740855175586330347343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166531160570117057553564895 249796740855175586330347343)
        ·
          refine ⟨374695111282763379495521015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249796740855175586330347343 374695111282763379495521015)
          ·
            refine ⟨562042666924145069243281523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374695111282763379495521015 562042666924145069243281523)
            ·
              refine ⟨843064000386217603864922285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562042666924145069243281523 843064000386217603864922285)
              ·
                refine ⟨316149000144831601449345857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 843064000386217603864922285 316149000144831601449345857)
                ·
                  refine ⟨237111750108623701087009393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316149000144831601449345857 237111750108623701087009393)
                  ·
                    refine ⟨177833812581467775815257045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 237111750108623701087009393 177833812581467775815257045)
                    ·
                      refine ⟨4167979982378150995670087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177833812581467775815257045 4167979982378150995670087)
                      ·
                        rfl

theorem cell23_8117112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_8117112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117112 prefixEnd_8117112 := by exact prefixLift 8117112
  have htrace : WordTrace (prefixWord ++ tailWord_8117112) baseStart_8117112 baseEnd_8117112 := by
    simpa [prefixWord, tailWord_8117112, baseEnd_8117112] using wordTrace_append hprefix tailTrace_8117112
  have hstable : (prefixWord ++ tailWord_8117112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117112).length < 2 ^ (prefixWord ++ tailWord_8117112).sum := by decide
  have hdescent : baseEnd_8117112 < baseStart_8117112 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117130 : List Nat := [3, 1, 2, 4, 1, 2, 1, 2, 3, 2, 2]
def baseStart_8117130 : Nat := 118140960795 + 8117130 * 2 ^ 59
def prefixEnd_8117130 : Nat := 4983230072969 + 3 ^ 40 * 8117130 * 2
def baseEnd_8117130 : Nat := 4167989225029931925245005

theorem tailTrace_8117130 : CollatzResearch.WordTrace tailWord_8117130 prefixEnd_8117130 4167989225029931925245005 := by
  unfold tailWord_8117130
  simp only [CollatzResearch.WordTrace]
  refine ⟨74014013270757945070123211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197370702055354520186995229 74014013270757945070123211)
  ·
    refine ⟨111021019906136917605184817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74014013270757945070123211 111021019906136917605184817)
    ·
      refine ⟨83265764929602688203888613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111021019906136917605184817 83265764929602688203888613)
      ·
        refine ⟨15612330924300504038229115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83265764929602688203888613 15612330924300504038229115)
        ·
          refine ⟨23418496386450756057343673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15612330924300504038229115 23418496386450756057343673)
          ·
            refine ⟨17563872289838067043007755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23418496386450756057343673 17563872289838067043007755)
            ·
              refine ⟨26345808434757100564511633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17563872289838067043007755 26345808434757100564511633)
              ·
                refine ⟨19759356326067825423383725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26345808434757100564511633 19759356326067825423383725)
                ·
                  refine ⟨7409758622275434533768897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19759356326067825423383725 7409758622275434533768897)
                  ·
                    refine ⟨5557318966706575900326673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7409758622275434533768897 5557318966706575900326673)
                    ·
                      refine ⟨4167989225029931925245005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5557318966706575900326673 4167989225029931925245005)
                      ·
                        rfl

theorem cell23_8117130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_8117130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117130 prefixEnd_8117130 := by exact prefixLift 8117130
  have htrace : WordTrace (prefixWord ++ tailWord_8117130) baseStart_8117130 baseEnd_8117130 := by
    simpa [prefixWord, tailWord_8117130, baseEnd_8117130] using wordTrace_append hprefix tailTrace_8117130
  have hstable : (prefixWord ++ tailWord_8117130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117130).length < 2 ^ (prefixWord ++ tailWord_8117130).sum := by decide
  have hdescent : baseEnd_8117130 < baseStart_8117130 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117174 : List Nat := [5, 1, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_8117174 : Nat := 118140960795 + 8117174 * 2 ^ 59
def prefixEnd_8117174 : Nat := 4983230072969 + 3 ^ 40 * 8117174 * 2
def baseEnd_8117174 : Nat := 1389337272726243251031601

theorem tailTrace_8117174 : CollatzResearch.WordTrace tailWord_8117174 prefixEnd_8117174 1389337272726243251031601 := by
  unfold tailWord_8117174
  simp only [CollatzResearch.WordTrace]
  refine ⟨18503603618429523487193411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197371771929914917196729717 18503603618429523487193411)
  ·
    refine ⟨27755405427644285230790117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18503603618429523487193411 27755405427644285230790117)
    ·
      refine ⟨5204138517683303480773147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27755405427644285230790117 5204138517683303480773147)
      ·
        refine ⟨7806207776524955221159721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5204138517683303480773147 7806207776524955221159721)
        ·
          refine ⟨5854655832393716415869791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7806207776524955221159721 5854655832393716415869791)
          ·
            refine ⟨8781983748590574623804687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5854655832393716415869791 8781983748590574623804687)
            ·
              refine ⟨13172975622885861935707031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8781983748590574623804687 13172975622885861935707031)
              ·
                refine ⟨19759463434328792903560547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13172975622885861935707031 19759463434328792903560547)
                ·
                  refine ⟨29639195151493189355340821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19759463434328792903560547 29639195151493189355340821)
                  ·
                    refine ⟨1389337272726243251031601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29639195151493189355340821 1389337272726243251031601)
                    ·
                      rfl

theorem cell23_8117174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_8117174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117174 prefixEnd_8117174 := by exact prefixLift 8117174
  have htrace : WordTrace (prefixWord ++ tailWord_8117174) baseStart_8117174 baseEnd_8117174 := by
    simpa [prefixWord, tailWord_8117174, baseEnd_8117174] using wordTrace_append hprefix tailTrace_8117174
  have hstable : (prefixWord ++ tailWord_8117174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117174).length < 2 ^ (prefixWord ++ tailWord_8117174).sum := by decide
  have hdescent : baseEnd_8117174 < baseStart_8117174 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117189 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 3, 6, 3]
def baseStart_8117189 : Nat := 118140960795 + 8117189 * 2 ^ 59
def prefixEnd_8117189 : Nat := 4983230072969 + 3 ^ 40 * 8117189 * 2
def baseEnd_8117189 : Nat := 4168019520388547194407233

theorem tailTrace_8117189 : CollatzResearch.WordTrace tailWord_8117189 prefixEnd_8117189 4168019520388547194407233 := by
  unfold tailWord_8117189
  simp only [CollatzResearch.WordTrace]
  refine ⟨296058204989818033356890621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197372136659878688904593747 296058204989818033356890621)
  ·
    refine ⟨111021826871181762508833983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296058204989818033356890621 111021826871181762508833983)
    ·
      refine ⟨166532740306772643763250975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111021826871181762508833983 166532740306772643763250975)
      ·
        refine ⟨249799110460158965644876463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166532740306772643763250975 249799110460158965644876463)
        ·
          refine ⟨374698665690238448467314695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249799110460158965644876463 374698665690238448467314695)
          ·
            refine ⟨562047998535357672700972043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374698665690238448467314695 562047998535357672700972043)
            ·
              refine ⟨843071997803036509051458065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562047998535357672700972043 843071997803036509051458065)
              ·
                refine ⟨632303998352277381788593549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843071997803036509051458065 632303998352277381788593549)
                ·
                  refine ⟨237113999382104018170722581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632303998352277381788593549 237113999382104018170722581)
                  ·
                    refine ⟨11114718721036125851752621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 237113999382104018170722581 11114718721036125851752621)
                    ·
                      refine ⟨4168019520388547194407233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11114718721036125851752621 4168019520388547194407233)
                      ·
                        rfl

theorem cell23_8117189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_8117189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117189 prefixEnd_8117189 := by exact prefixLift 8117189
  have htrace : WordTrace (prefixWord ++ tailWord_8117189) baseStart_8117189 baseEnd_8117189 := by
    simpa [prefixWord, tailWord_8117189, baseEnd_8117189] using wordTrace_append hprefix tailTrace_8117189
  have hstable : (prefixWord ++ tailWord_8117189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117189).length < 2 ^ (prefixWord ++ tailWord_8117189).sum := by decide
  have hdescent : baseEnd_8117189 < baseStart_8117189 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117219 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 7]
def baseStart_8117219 : Nat := 118140960795 + 8117219 * 2 ^ 59
def prefixEnd_8117219 : Nat := 4983230072969 + 3 ^ 40 * 8117219 * 2
def baseEnd_8117219 : Nat := 4168034924808182077032095

theorem tailTrace_8117219 : CollatzResearch.WordTrace tailWord_8117219 prefixEnd_8117219 4168034924808182077032095 := by
  unfold tailWord_8117219
  simp only [CollatzResearch.WordTrace]
  refine ⟨296059299179709348480482711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197372866119806232320321807 296059299179709348480482711)
  ·
    refine ⟨444088948769564022720724067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296059299179709348480482711 444088948769564022720724067)
    ·
      refine ⟨666133423154346034081086101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444088948769564022720724067 666133423154346034081086101)
      ·
        refine ⟨31225004210359970347550911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 666133423154346034081086101 31225004210359970347550911)
        ·
          refine ⟨46837506315539955521326367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31225004210359970347550911 46837506315539955521326367)
          ·
            refine ⟨70256259473309933281989551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46837506315539955521326367 70256259473309933281989551)
            ·
              refine ⟨105384389209964899922984327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70256259473309933281989551 105384389209964899922984327)
              ·
                refine ⟨158076583814947349884476491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105384389209964899922984327 158076583814947349884476491)
                ·
                  refine ⟨237114875722421024826714737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158076583814947349884476491 237114875722421024826714737)
                  ·
                    refine ⟨177836156791815768620036053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 237114875722421024826714737 177836156791815768620036053)
                    ·
                      refine ⟨4168034924808182077032095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177836156791815768620036053 4168034924808182077032095)
                      ·
                        rfl

theorem cell23_8117219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_8117219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117219 prefixEnd_8117219 := by exact prefixLift 8117219
  have htrace : WordTrace (prefixWord ++ tailWord_8117219) baseStart_8117219 baseEnd_8117219 := by
    simpa [prefixWord, tailWord_8117219, baseEnd_8117219] using wordTrace_append hprefix tailTrace_8117219
  have hstable : (prefixWord ++ tailWord_8117219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117219).length < 2 ^ (prefixWord ++ tailWord_8117219).sum := by decide
  have hdescent : baseEnd_8117219 < baseStart_8117219 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117226 : List Nat := [3, 1, 3, 1, 2, 2, 3, 1, 7]
def baseStart_8117226 : Nat := 118140960795 + 8117226 * 2 ^ 59
def prefixEnd_8117226 : Nat := 4983230072969 + 3 ^ 40 * 8117226 * 2
def baseEnd_8117226 : Nat := 463115391019195949960507

theorem tailTrace_8117226 : CollatzResearch.WordTrace tailWord_8117226 prefixEnd_8117226 463115391019195949960507 := by
  unfold tailWord_8117226
  simp only [CollatzResearch.WordTrace]
  refine ⟨74014888622670997168996883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197373036327122659117325021 74014888622670997168996883)
  ·
    refine ⟨111022332934006495753495325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74014888622670997168996883 111022332934006495753495325)
    ·
      refine ⟨41633374850252435907560747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111022332934006495753495325 41633374850252435907560747)
      ·
        refine ⟨62450062275378653861341121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41633374850252435907560747 62450062275378653861341121)
        ·
          refine ⟨46837546706533990396005841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62450062275378653861341121 46837546706533990396005841)
          ·
            refine ⟨35128160029900492797004381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46837546706533990396005841 35128160029900492797004381)
            ·
              refine ⟨13173060011212684798876643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35128160029900492797004381 13173060011212684798876643)
              ·
                refine ⟨19759590016819027198314965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13173060011212684798876643 19759590016819027198314965)
                ·
                  refine ⟨463115391019195949960507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19759590016819027198314965 463115391019195949960507)
                  ·
                    rfl

theorem cell23_8117226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 7].length) (baseStart_8117226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117226 prefixEnd_8117226 := by exact prefixLift 8117226
  have htrace : WordTrace (prefixWord ++ tailWord_8117226) baseStart_8117226 baseEnd_8117226 := by
    simpa [prefixWord, tailWord_8117226, baseEnd_8117226] using wordTrace_append hprefix tailTrace_8117226
  have hstable : (prefixWord ++ tailWord_8117226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117226).length < 2 ^ (prefixWord ++ tailWord_8117226).sum := by decide
  have hdescent : baseEnd_8117226 < baseStart_8117226 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117256 : List Nat := [2, 1, 3, 2, 1, 3, 1, 3, 2, 5]
def baseStart_8117256 : Nat := 118140960795 + 8117256 * 2 ^ 59
def prefixEnd_8117256 : Nat := 4983230072969 + 3 ^ 40 * 8117256 * 2
def baseEnd_8117256 : Nat := 1389351307864132810756475

theorem tailTrace_8117256 : CollatzResearch.WordTrace tailWord_8117256 prefixEnd_8117256 1389351307864132810756475 := by
  unfold tailWord_8117256
  simp only [CollatzResearch.WordTrace]
  refine ⟨148030324340287651899789811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197373765787050202533053081 148030324340287651899789811)
  ·
    refine ⟨222045486510431477849684717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148030324340287651899789811 222045486510431477849684717)
    ·
      refine ⟨83267057441411804193631769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222045486510431477849684717 83267057441411804193631769)
      ·
        refine ⟨62450293081058853145223827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83267057441411804193631769 62450293081058853145223827)
        ·
          refine ⟨93675439621588279717835741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62450293081058853145223827 93675439621588279717835741)
          ·
            refine ⟨35128289858095604894188403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93675439621588279717835741 35128289858095604894188403)
            ·
              refine ⟨52692434787143407341282605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35128289858095604894188403 52692434787143407341282605)
              ·
                refine ⟨19759663045178777752980977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52692434787143407341282605 19759663045178777752980977)
                ·
                  refine ⟨14819747283884083314735733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19759663045178777752980977 14819747283884083314735733)
                  ·
                    refine ⟨1389351307864132810756475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14819747283884083314735733 1389351307864132810756475)
                    ·
                      rfl

theorem cell23_8117256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_8117256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117256 prefixEnd_8117256 := by exact prefixLift 8117256
  have htrace : WordTrace (prefixWord ++ tailWord_8117256) baseStart_8117256 baseEnd_8117256 := by
    simpa [prefixWord, tailWord_8117256, baseEnd_8117256] using wordTrace_append hprefix tailTrace_8117256
  have hstable : (prefixWord ++ tailWord_8117256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117256).length < 2 ^ (prefixWord ++ tailWord_8117256).sum := by decide
  have hdescent : baseEnd_8117256 < baseStart_8117256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117277 : List Nat := [1, 4, 2, 2, 3, 2, 2, 2, 5]
def baseStart_8117277 : Nat := 118140960795 + 8117277 * 2 ^ 59
def prefixEnd_8117277 : Nat := 4983230072969 + 3 ^ 40 * 8117277 * 2
def baseEnd_8117277 : Nat := 463118300742904761122981

theorem tailTrace_8117277 : CollatzResearch.WordTrace tailWord_8117277 prefixEnd_8117277 463118300742904761122981 := by
  unfold tailWord_8117277
  simp only [CollatzResearch.WordTrace]
  refine ⟨296061414613499224386094085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197374276408999482924062723 296061414613499224386094085)
  ·
    refine ⟨55511515240031104572392641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296061414613499224386094085 55511515240031104572392641)
    ·
      refine ⟨41633636430023328429294481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55511515240031104572392641 41633636430023328429294481)
      ·
        refine ⟨31225227322517496321970861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41633636430023328429294481 31225227322517496321970861)
        ·
          refine ⟨11709460245944061120739073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31225227322517496321970861 11709460245944061120739073)
          ·
            refine ⟨8782095184458045840554305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11709460245944061120739073 8782095184458045840554305)
            ·
              refine ⟨6586571388343534380415729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8782095184458045840554305 6586571388343534380415729)
              ·
                refine ⟨4939928541257650785311797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6586571388343534380415729 4939928541257650785311797)
                ·
                  refine ⟨463118300742904761122981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4939928541257650785311797 463118300742904761122981)
                  ·
                    rfl

theorem cell23_8117277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_8117277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117277 prefixEnd_8117277 := by exact prefixLift 8117277
  have htrace : WordTrace (prefixWord ++ tailWord_8117277) baseStart_8117277 baseEnd_8117277 := by
    simpa [prefixWord, tailWord_8117277, baseEnd_8117277] using wordTrace_append hprefix tailTrace_8117277
  have hstable : (prefixWord ++ tailWord_8117277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117277).length < 2 ^ (prefixWord ++ tailWord_8117277).sum := by decide
  have hdescent : baseEnd_8117277 < baseStart_8117277 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117296 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 3]
def baseStart_8117296 : Nat := 118140960795 + 8117296 * 2 ^ 59
def prefixEnd_8117296 : Nat := 4983230072969 + 3 ^ 40 * 8117296 * 2
def baseEnd_8117296 : Nat := 4168074462818578275769241

theorem tailTrace_8117296 : CollatzResearch.WordTrace tailWord_8117296 prefixEnd_8117296 4168074462818578275769241 := by
  unfold tailWord_8117296
  simp only [CollatzResearch.WordTrace]
  refine ⟨148031053800215195315517871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197374738400286927087357161 148031053800215195315517871)
  ·
    refine ⟨222046580700322792973276807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148031053800215195315517871 222046580700322792973276807)
    ·
      refine ⟨333069871050484189459915211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222046580700322792973276807 333069871050484189459915211)
      ·
        refine ⟨499604806575726284189872817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333069871050484189459915211 499604806575726284189872817)
        ·
          refine ⟨374703604931794713142404613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499604806575726284189872817 374703604931794713142404613)
          ·
            refine ⟨70256925924711508714200865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 374703604931794713142404613 70256925924711508714200865)
            ·
              refine ⟨52692694443533631535650649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70256925924711508714200865 52692694443533631535650649)
              ·
                refine ⟨39519520832650223651737987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52692694443533631535650649 39519520832650223651737987)
                ·
                  refine ⟨59279281248975335477606981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39519520832650223651737987 59279281248975335477606981)
                  ·
                    refine ⟨11114865234182875402051309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59279281248975335477606981 11114865234182875402051309)
                    ·
                      refine ⟨4168074462818578275769241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11114865234182875402051309 4168074462818578275769241)
                      ·
                        rfl

theorem cell23_8117296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 3].length) (baseStart_8117296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117296 prefixEnd_8117296 := by exact prefixLift 8117296
  have htrace : WordTrace (prefixWord ++ tailWord_8117296) baseStart_8117296 baseEnd_8117296 := by
    simpa [prefixWord, tailWord_8117296, baseEnd_8117296] using wordTrace_append hprefix tailTrace_8117296
  have hstable : (prefixWord ++ tailWord_8117296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117296).length < 2 ^ (prefixWord ++ tailWord_8117296).sum := by decide
  have hdescent : baseEnd_8117296 < baseStart_8117296 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117299 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 10]
def baseStart_8117299 : Nat := 118140960795 + 8117299 * 2 ^ 59
def prefixEnd_8117299 : Nat := 4983230072969 + 3 ^ 40 * 8117299 * 2
def baseEnd_8117299 : Nat := 463119555917837973781303

theorem tailTrace_8117299 : CollatzResearch.WordTrace tailWord_8117299 prefixEnd_8117299 463119555917837973781303 := by
  unfold tailWord_8117299
  simp only [CollatzResearch.WordTrace]
  refine ⟨296062217019419522143394951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197374811346279681428929967 296062217019419522143394951)
  ·
    refine ⟨444093325529129283215092427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296062217019419522143394951 444093325529129283215092427)
    ·
      refine ⟨666139988293693924822638641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444093325529129283215092427 666139988293693924822638641)
      ·
        refine ⟨499604991220270443616978981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666139988293693924822638641 499604991220270443616978981)
        ·
          refine ⟨93675935853800708178183559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 499604991220270443616978981 93675935853800708178183559)
          ·
            refine ⟨140513903780701062267275339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93675935853800708178183559 140513903780701062267275339)
            ·
              refine ⟨210770855671051593400913009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140513903780701062267275339 210770855671051593400913009)
              ·
                refine ⟨158078141753288695050684757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210770855671051593400913009 158078141753288695050684757)
                ·
                  refine ⟨463119555917837973781303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 158078141753288695050684757 463119555917837973781303)
                  ·
                    rfl

theorem cell23_8117299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 10].length) (baseStart_8117299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117299 prefixEnd_8117299 := by exact prefixLift 8117299
  have htrace : WordTrace (prefixWord ++ tailWord_8117299) baseStart_8117299 baseEnd_8117299 := by
    simpa [prefixWord, tailWord_8117299, baseEnd_8117299] using wordTrace_append hprefix tailTrace_8117299
  have hstable : (prefixWord ++ tailWord_8117299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117299).length < 2 ^ (prefixWord ++ tailWord_8117299).sum := by decide
  have hdescent : baseEnd_8117299 < baseStart_8117299 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117310 : List Nat := [4, 2, 1, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_8117310 : Nat := 118140960795 + 8117310 * 2 ^ 59
def prefixEnd_8117310 : Nat := 4983230072969 + 3 ^ 40 * 8117310 * 2
def baseEnd_8117310 : Nat := 4168081651547741220994177

theorem tailTrace_8117310 : CollatzResearch.WordTrace tailWord_8117310 prefixEnd_8117310 4168081651547741220994177 := by
  unfold tailWord_8117310
  simp only [CollatzResearch.WordTrace]
  refine ⟨37007827277797458877755673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197375078814919780681363589 37007827277797458877755673)
  ·
    refine ⟨27755870458348094158316755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37007827277797458877755673 27755870458348094158316755)
    ·
      refine ⟨41633805687522141237475133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27755870458348094158316755 41633805687522141237475133)
      ·
        refine ⟨15612677132820802964053175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41633805687522141237475133 15612677132820802964053175)
        ·
          refine ⟨23419015699231204446079763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15612677132820802964053175 23419015699231204446079763)
          ·
            refine ⟨35128523548846806669119645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23419015699231204446079763 35128523548846806669119645)
            ·
              refine ⟨13173196330817552500919867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35128523548846806669119645 13173196330817552500919867)
              ·
                refine ⟨19759794496226328751379801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13173196330817552500919867 19759794496226328751379801)
                ·
                  refine ⟨14819845872169746563534851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19759794496226328751379801 14819845872169746563534851)
                  ·
                    refine ⟨22229768808254619845302277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14819845872169746563534851 22229768808254619845302277)
                    ·
                      refine ⟨4168081651547741220994177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22229768808254619845302277 4168081651547741220994177)
                      ·
                        rfl

theorem cell23_8117310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_8117310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117310 prefixEnd_8117310 := by exact prefixLift 8117310
  have htrace : WordTrace (prefixWord ++ tailWord_8117310) baseStart_8117310 baseEnd_8117310 := by
    simpa [prefixWord, tailWord_8117310, baseEnd_8117310] using wordTrace_append hprefix tailTrace_8117310
  have hstable : (prefixWord ++ tailWord_8117310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117310).length < 2 ^ (prefixWord ++ tailWord_8117310).sum := by decide
  have hdescent : baseEnd_8117310 < baseStart_8117310 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117320 : List Nat := [2, 1, 3, 1, 1, 1, 6, 3, 1, 4]
def baseStart_8117320 : Nat := 118140960795 + 8117320 * 2 ^ 59
def prefixEnd_8117320 : Nat := 4983230072969 + 3 ^ 40 * 8117320 * 2
def baseEnd_8117320 : Nat := 1389362262118095393956377

theorem tailTrace_8117320 : CollatzResearch.WordTrace tailWord_8117320 prefixEnd_8117320 1389362262118095393956377 := by
  unfold tailWord_8117320
  simp only [CollatzResearch.WordTrace]
  refine ⟨148031491476171721364954707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197375321968228961819939609 148031491476171721364954707)
  ·
    refine ⟨222047237214257582047432061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148031491476171721364954707 222047237214257582047432061)
    ·
      refine ⟨83267713955346593267787023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222047237214257582047432061 83267713955346593267787023)
      ·
        refine ⟨124901570933019889901680535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83267713955346593267787023 124901570933019889901680535)
        ·
          refine ⟨187352356399529834852520803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124901570933019889901680535 187352356399529834852520803)
          ·
            refine ⟨281028534599294752278781205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187352356399529834852520803 281028534599294752278781205)
            ·
              refine ⟨13173212559341941513067869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 281028534599294752278781205 13173212559341941513067869)
              ·
                refine ⟨4939954709753228067400451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13173212559341941513067869 4939954709753228067400451)
                ·
                  refine ⟨7409932064629842101100677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4939954709753228067400451 7409932064629842101100677)
                  ·
                    refine ⟨1389362262118095393956377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7409932064629842101100677 1389362262118095393956377)
                    ·
                      rfl

theorem cell23_8117320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_8117320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117320 prefixEnd_8117320 := by exact prefixLift 8117320
  have htrace : WordTrace (prefixWord ++ tailWord_8117320) baseStart_8117320 baseEnd_8117320 := by
    simpa [prefixWord, tailWord_8117320, baseEnd_8117320] using wordTrace_append hprefix tailTrace_8117320
  have hstable : (prefixWord ++ tailWord_8117320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117320).length < 2 ^ (prefixWord ++ tailWord_8117320).sum := by decide
  have hdescent : baseEnd_8117320 < baseStart_8117320 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117353 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 1, 5, 2]
def baseStart_8117353 : Nat := 118140960795 + 8117353 * 2 ^ 59
def prefixEnd_8117353 : Nat := 4983230072969 + 3 ^ 40 * 8117353 * 2
def baseEnd_8117353 : Nat := 4168103731215884552756479

theorem tailTrace_8117353 : CollatzResearch.WordTrace tailWord_8117353 prefixEnd_8117353 4168103731215884552756479 := by
  unfold tailWord_8117353
  simp only [CollatzResearch.WordTrace]
  refine ⟨296064186561223889365860713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197376124374149259577240475 296064186561223889365860713)
  ·
    refine ⟨222048139920917917024395535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296064186561223889365860713 222048139920917917024395535)
    ·
      refine ⟨333072209881376875536593303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222048139920917917024395535 333072209881376875536593303)
      ·
        refine ⟨499608314822065313304889955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333072209881376875536593303 499608314822065313304889955)
        ·
          refine ⟨749412472233097969957334933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499608314822065313304889955 749412472233097969957334933)
          ·
            refine ⟨35128709635926467341750075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 749412472233097969957334933 35128709635926467341750075)
            ·
              refine ⟨52693064453889701012625113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35128709635926467341750075 52693064453889701012625113)
              ·
                refine ⟨39519798340417275759468835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52693064453889701012625113 39519798340417275759468835)
                ·
                  refine ⟨59279697510625913639203253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39519798340417275759468835 59279697510625913639203253)
                  ·
                    refine ⟨5557471641621179403675305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59279697510625913639203253 5557471641621179403675305)
                    ·
                      refine ⟨4168103731215884552756479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5557471641621179403675305 4168103731215884552756479)
                      ·
                        rfl

theorem cell23_8117353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 5, 2].length) (baseStart_8117353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117353 prefixEnd_8117353 := by exact prefixLift 8117353
  have htrace : WordTrace (prefixWord ++ tailWord_8117353) baseStart_8117353 baseEnd_8117353 := by
    simpa [prefixWord, tailWord_8117353, baseEnd_8117353] using wordTrace_append hprefix tailTrace_8117353
  have hstable : (prefixWord ++ tailWord_8117353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117353).length < 2 ^ (prefixWord ++ tailWord_8117353).sum := by decide
  have hdescent : baseEnd_8117353 < baseStart_8117353 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117376 : List Nat := [2, 1, 1, 2, 1, 3, 2, 4, 1, 6]
def baseStart_8117376 : Nat := 118140960795 + 8117376 * 2 ^ 59
def prefixEnd_8117376 : Nat := 4983230072969 + 3 ^ 40 * 8117376 * 2
def baseEnd_8117376 : Nat := 1389371847090312654256291

theorem tailTrace_8117376 : CollatzResearch.WordTrace tailWord_8117376 prefixEnd_8117376 1389371847090312654256291 := by
  unfold tailWord_8117376
  simp only [CollatzResearch.WordTrace]
  refine ⟨148032512720070282146973991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197376683626760376195965321 148032512720070282146973991)
  ·
    refine ⟨222048769080105423220460987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148032512720070282146973991 222048769080105423220460987)
    ·
      refine ⟨333073153620158134830691481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222048769080105423220460987 333073153620158134830691481)
      ·
        refine ⟨249804865215118601123018611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333073153620158134830691481 249804865215118601123018611)
        ·
          refine ⟨374707297822677901684527917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249804865215118601123018611 374707297822677901684527917)
          ·
            refine ⟨140515236683504213131697969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374707297822677901684527917 140515236683504213131697969)
            ·
              refine ⟨105386427512628159848773477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140515236683504213131697969 105386427512628159848773477)
              ·
                refine ⟨19759955158617779971645027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105386427512628159848773477 19759955158617779971645027)
                ·
                  refine ⟨29639932737926669957467541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19759955158617779971645027 29639932737926669957467541)
                  ·
                    refine ⟨1389371847090312654256291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29639932737926669957467541 1389371847090312654256291)
                    ·
                      rfl

theorem cell23_8117376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 1, 6].length) (baseStart_8117376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117376 prefixEnd_8117376 := by exact prefixLift 8117376
  have htrace : WordTrace (prefixWord ++ tailWord_8117376) baseStart_8117376 baseEnd_8117376 := by
    simpa [prefixWord, tailWord_8117376, baseEnd_8117376] using wordTrace_append hprefix tailTrace_8117376
  have hstable : (prefixWord ++ tailWord_8117376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117376).length < 2 ^ (prefixWord ++ tailWord_8117376).sum := by decide
  have hdescent : baseEnd_8117376 < baseStart_8117376 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117433 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 3, 3, 3]
def baseStart_8117433 : Nat := 118140960795 + 8117433 * 2 ^ 59
def prefixEnd_8117433 : Nat := 4983230072969 + 3 ^ 40 * 8117433 * 2
def baseEnd_8117433 : Nat := 4168144809668244239756111

theorem tailTrace_8117433 : CollatzResearch.WordTrace tailWord_8117433 prefixEnd_8117433 4168144809668244239756111 := by
  unfold tailWord_8117433
  simp only [CollatzResearch.WordTrace]
  refine ⟨296067104400934063028772953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197378069600622708685848635 296067104400934063028772953)
  ·
    refine ⟨222050328300700547271579715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296067104400934063028772953 222050328300700547271579715)
    ·
      refine ⟨333075492451050820907369573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222050328300700547271579715 333075492451050820907369573)
      ·
        refine ⟨62451654834572028920131795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333075492451050820907369573 62451654834572028920131795)
        ·
          refine ⟨93677482251858043380197693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62451654834572028920131795 93677482251858043380197693)
          ·
            refine ⟨35129055844446766267574135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93677482251858043380197693 35129055844446766267574135)
            ·
              refine ⟨52693583766670149401361203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35129055844446766267574135 52693583766670149401361203)
              ·
                refine ⟨79040375650005224102041805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52693583766670149401361203 79040375650005224102041805)
                ·
                  refine ⟨29640140868751959038265677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79040375650005224102041805 29640140868751959038265677)
                  ·
                    refine ⟨11115052825781984639349629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29640140868751959038265677 11115052825781984639349629)
                    ·
                      refine ⟨4168144809668244239756111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11115052825781984639349629 4168144809668244239756111)
                      ·
                        rfl

theorem cell23_8117433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_8117433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117433 prefixEnd_8117433 := by exact prefixLift 8117433
  have htrace : WordTrace (prefixWord ++ tailWord_8117433) baseStart_8117433 baseEnd_8117433 := by
    simpa [prefixWord, tailWord_8117433, baseEnd_8117433] using wordTrace_append hprefix tailTrace_8117433
  have hstable : (prefixWord ++ tailWord_8117433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117433).length < 2 ^ (prefixWord ++ tailWord_8117433).sum := by decide
  have hdescent : baseEnd_8117433 < baseStart_8117433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117503 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 4]
def baseStart_8117503 : Nat := 118140960795 + 8117503 * 2 ^ 59
def prefixEnd_8117503 : Nat := 4983230072969 + 3 ^ 40 * 8117503 * 2
def baseEnd_8117503 : Nat := 4168180753314058965880789

theorem tailTrace_8117503 : CollatzResearch.WordTrace tailWord_8117503 prefixEnd_8117503 4168180753314058965880789 := by
  unfold tailWord_8117503
  simp only [CollatzResearch.WordTrace]
  refine ⟨296069657510680464983821163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197379771673786976655880775 296069657510680464983821163)
  ·
    refine ⟨444104486266020697475731745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296069657510680464983821163 444104486266020697475731745)
    ·
      refine ⟨333078364699515523106798809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444104486266020697475731745 333078364699515523106798809)
      ·
        refine ⟨249808773524636642330099107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333078364699515523106798809 249808773524636642330099107)
        ·
          refine ⟨374713160286954963495148661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249808773524636642330099107 374713160286954963495148661)
          ·
            refine ⟨35129358776902027827670187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 374713160286954963495148661 35129358776902027827670187)
            ·
              refine ⟨52694038165353041741505281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35129358776902027827670187 52694038165353041741505281)
              ·
                refine ⟨39520528624014781306128961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52694038165353041741505281 39520528624014781306128961)
                ·
                  refine ⟨29640396468011085979596721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39520528624014781306128961 29640396468011085979596721)
                  ·
                    refine ⟨22230297351008314484697541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29640396468011085979596721 22230297351008314484697541)
                    ·
                      refine ⟨4168180753314058965880789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22230297351008314484697541 4168180753314058965880789)
                      ·
                        rfl

theorem cell23_8117503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_8117503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117503 prefixEnd_8117503 := by exact prefixLift 8117503
  have htrace : WordTrace (prefixWord ++ tailWord_8117503) baseStart_8117503 baseEnd_8117503 := by
    simpa [prefixWord, tailWord_8117503, baseEnd_8117503] using wordTrace_append hprefix tailTrace_8117503
  have hstable : (prefixWord ++ tailWord_8117503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117503).length < 2 ^ (prefixWord ++ tailWord_8117503).sum := by decide
  have hdescent : baseEnd_8117503 < baseStart_8117503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117507 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 4, 2, 2]
def baseStart_8117507 : Nat := 118140960795 + 8117507 * 2 ^ 59
def prefixEnd_8117507 : Nat := 4983230072969 + 3 ^ 40 * 8117507 * 2
def baseEnd_8117507 : Nat := 4168182807236676950230771

theorem tailTrace_8117507 : CollatzResearch.WordTrace tailWord_8117507 prefixEnd_8117507 4168182807236676950230771 := by
  unfold tailWord_8117507
  simp only [CollatzResearch.WordTrace]
  refine ⟨296069803402665973666966775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197379868935110649111311183 296069803402665973666966775)
  ·
    refine ⟨444104705103998960500450163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296069803402665973666966775 444104705103998960500450163)
    ·
      refine ⟨666157057655998440750675245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444104705103998960500450163 666157057655998440750675245)
      ·
        refine ⟨249808896620999415281503217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 666157057655998440750675245 249808896620999415281503217)
        ·
          refine ⟨187356672465749561461127413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249808896620999415281503217 187356672465749561461127413)
          ·
            refine ⟨17564688043664021386980695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187356672465749561461127413 17564688043664021386980695)
            ·
              refine ⟨26347032065496032080471043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17564688043664021386980695 26347032065496032080471043)
              ·
                refine ⟨39520548098244048120706565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26347032065496032080471043 39520548098244048120706565)
                ·
                  refine ⟨7410102768420759022632481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39520548098244048120706565 7410102768420759022632481)
                  ·
                    refine ⟨5557577076315569266974361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7410102768420759022632481 5557577076315569266974361)
                    ·
                      refine ⟨4168182807236676950230771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5557577076315569266974361 4168182807236676950230771)
                      ·
                        rfl

theorem cell23_8117507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 2, 2].length) (baseStart_8117507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117507 prefixEnd_8117507 := by exact prefixLift 8117507
  have htrace : WordTrace (prefixWord ++ tailWord_8117507) baseStart_8117507 baseEnd_8117507 := by
    simpa [prefixWord, tailWord_8117507, baseEnd_8117507] using wordTrace_append hprefix tailTrace_8117507
  have hstable : (prefixWord ++ tailWord_8117507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117507).length < 2 ^ (prefixWord ++ tailWord_8117507).sum := by decide
  have hdescent : baseEnd_8117507 < baseStart_8117507 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117513 : List Nat := [1, 2, 1, 1, 3, 3, 4, 1, 7]
def baseStart_8117513 : Nat := 118140960795 + 8117513 * 2 ^ 59
def prefixEnd_8117513 : Nat := 4983230072969 + 3 ^ 40 * 8117513 * 2
def baseEnd_8117513 : Nat := 463131765346733769639527

theorem tailTrace_8117513 : CollatzResearch.WordTrace tailWord_8117513 prefixEnd_8117513 463131765346733769639527 := by
  unfold tailWord_8117513
  simp only [CollatzResearch.WordTrace]
  refine ⟨296070022240644236691685193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197380014827096157794456795 296070022240644236691685193)
  ·
    refine ⟨222052516680483177518763895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296070022240644236691685193 222052516680483177518763895)
    ·
      refine ⟨333078775020724766278145843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222052516680483177518763895 333078775020724766278145843)
      ·
        refine ⟨499618162531087149417218765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333078775020724766278145843 499618162531087149417218765)
        ·
          refine ⟨187356810949157681031457037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 499618162531087149417218765 187356810949157681031457037)
          ·
            refine ⟨70258804105934130386796389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187356810949157681031457037 70258804105934130386796389)
            ·
              refine ⟨13173525769862649447524323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70258804105934130386796389 13173525769862649447524323)
              ·
                refine ⟨19760288654793974171286485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13173525769862649447524323 19760288654793974171286485)
                ·
                  refine ⟨463131765346733769639527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19760288654793974171286485 463131765346733769639527)
                  ·
                    rfl

theorem cell23_8117513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 7].length) (baseStart_8117513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117513 prefixEnd_8117513 := by exact prefixLift 8117513
  have htrace : WordTrace (prefixWord ++ tailWord_8117513) baseStart_8117513 baseEnd_8117513 := by
    simpa [prefixWord, tailWord_8117513, baseEnd_8117513] using wordTrace_append hprefix tailTrace_8117513
  have hstable : (prefixWord ++ tailWord_8117513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117513).length < 2 ^ (prefixWord ++ tailWord_8117513).sum := by decide
  have hdescent : baseEnd_8117513 < baseStart_8117513 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117593 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 2, 4, 4]
def baseStart_8117593 : Nat := 118140960795 + 8117593 * 2 ^ 59
def prefixEnd_8117593 : Nat := 4983230072969 + 3 ^ 40 * 8117593 * 2
def baseEnd_8117593 : Nat := 4168226966572963613755375

theorem tailTrace_8117593 : CollatzResearch.WordTrace tailWord_8117593 prefixEnd_8117593 4168226966572963613755375 := by
  unfold tailWord_8117593
  simp only [CollatzResearch.WordTrace]
  refine ⟨296072940080354410354597433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197381960053569606903064955 296072940080354410354597433)
  ·
    refine ⟨222054705060265807765948075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296072940080354410354597433 222054705060265807765948075)
    ·
      refine ⟨333082057590398711648922113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222054705060265807765948075 333082057590398711648922113)
      ·
        refine ⟨249811543192799033736691585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333082057590398711648922113 249811543192799033736691585)
        ·
          refine ⟨187358657394599275302518689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249811543192799033736691585 187358657394599275302518689)
          ·
            refine ⟨140518993045949456476889017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187358657394599275302518689 140518993045949456476889017)
            ·
              refine ⟨105389244784462092357666763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140518993045949456476889017 105389244784462092357666763)
              ·
                refine ⟨158083867176693138536500145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105389244784462092357666763 158083867176693138536500145)
                ·
                  refine ⟨118562900382519853902375109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158083867176693138536500145 118562900382519853902375109)
                  ·
                    refine ⟨22230543821722472606695333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118562900382519853902375109 22230543821722472606695333)
                    ·
                      refine ⟨4168226966572963613755375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22230543821722472606695333 4168226966572963613755375)
                      ·
                        rfl

theorem cell23_8117593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_8117593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117593 prefixEnd_8117593 := by exact prefixLift 8117593
  have htrace : WordTrace (prefixWord ++ tailWord_8117593) baseStart_8117593 baseEnd_8117593 := by
    simpa [prefixWord, tailWord_8117593, baseEnd_8117593] using wordTrace_append hprefix tailTrace_8117593
  have hstable : (prefixWord ++ tailWord_8117593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117593).length < 2 ^ (prefixWord ++ tailWord_8117593).sum := by decide
  have hdescent : baseEnd_8117593 < baseStart_8117593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117623 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 6]
def baseStart_8117623 : Nat := 118140960795 + 8117623 * 2 ^ 59
def prefixEnd_8117623 : Nat := 4983230072969 + 3 ^ 40 * 8117623 * 2
def baseEnd_8117623 : Nat := 4168242370992598496380237

theorem tailTrace_8117623 : CollatzResearch.WordTrace tailWord_8117623 prefixEnd_8117623 4168242370992598496380237 := by
  unfold tailWord_8117623
  simp only [CollatzResearch.WordTrace]
  refine ⟨296074034270245725478189523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197382689513497150318793015 296074034270245725478189523)
  ·
    refine ⟨444111051405368588217284285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296074034270245725478189523 444111051405368588217284285)
    ·
      refine ⟨166541644277013220581481607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444111051405368588217284285 166541644277013220581481607)
      ·
        refine ⟨249812466415519830872222411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166541644277013220581481607 249812466415519830872222411)
        ·
          refine ⟨374718699623279746308333617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249812466415519830872222411 374718699623279746308333617)
          ·
            refine ⟨281039024717459809731250213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374718699623279746308333617 281039024717459809731250213)
            ·
              refine ⟨52694817134523714324609415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281039024717459809731250213 52694817134523714324609415)
              ·
                refine ⟨79042225701785571486914123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52694817134523714324609415 79042225701785571486914123)
                ·
                  refine ⟨118563338552678357230371185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79042225701785571486914123 118563338552678357230371185)
                  ·
                    refine ⟨88922503914508767922778389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118563338552678357230371185 88922503914508767922778389)
                    ·
                      refine ⟨4168242370992598496380237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88922503914508767922778389 4168242370992598496380237)
                      ·
                        rfl

theorem cell23_8117623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_8117623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117623 prefixEnd_8117623 := by exact prefixLift 8117623
  have htrace : WordTrace (prefixWord ++ tailWord_8117623) baseStart_8117623 baseEnd_8117623 := by
    simpa [prefixWord, tailWord_8117623, baseEnd_8117623] using wordTrace_append hprefix tailTrace_8117623
  have hstable : (prefixWord ++ tailWord_8117623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117623).length < 2 ^ (prefixWord ++ tailWord_8117623).sum := by decide
  have hdescent : baseEnd_8117623 < baseStart_8117623 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117643 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 7]
def baseStart_8117643 : Nat := 118140960795 + 8117643 * 2 ^ 59
def prefixEnd_8117643 : Nat := 4983230072969 + 3 ^ 40 * 8117643 * 2
def baseEnd_8117643 : Nat := 4168252640605688418130145

theorem tailTrace_8117643 : CollatzResearch.WordTrace tailWord_8117643 prefixEnd_8117643 4168252640605688418130145 := by
  unfold tailWord_8117643
  simp only [CollatzResearch.WordTrace]
  refine ⟨296074763730173268893917583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197383175820115512595945055 296074763730173268893917583)
  ·
    refine ⟨444112145595259903340876375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296074763730173268893917583 444112145595259903340876375)
    ·
      refine ⟨666168218392889855011314563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444112145595259903340876375 666168218392889855011314563)
      ·
        refine ⟨999252327589334782516971845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666168218392889855011314563 999252327589334782516971845)
        ·
          refine ⟨187359811423000271721932221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 999252327589334782516971845 187359811423000271721932221)
          ·
            refine ⟨70259929283625101895724583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187359811423000271721932221 70259929283625101895724583)
            ·
              refine ⟨105389893925437652843586875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70259929283625101895724583 105389893925437652843586875)
              ·
                refine ⟨158084840888156479265380313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105389893925437652843586875 158084840888156479265380313)
                ·
                  refine ⟨118563630666117359449035235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158084840888156479265380313 118563630666117359449035235)
                  ·
                    refine ⟨177845445999176039173552853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118563630666117359449035235 177845445999176039173552853)
                    ·
                      refine ⟨4168252640605688418130145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177845445999176039173552853 4168252640605688418130145)
                      ·
                        rfl

theorem cell23_8117643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 7].length) (baseStart_8117643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117643 prefixEnd_8117643 := by exact prefixLift 8117643
  have htrace : WordTrace (prefixWord ++ tailWord_8117643) baseStart_8117643 baseEnd_8117643 := by
    simpa [prefixWord, tailWord_8117643, baseEnd_8117643] using wordTrace_append hprefix tailTrace_8117643
  have hstable : (prefixWord ++ tailWord_8117643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117643).length < 2 ^ (prefixWord ++ tailWord_8117643).sum := by decide
  have hdescent : baseEnd_8117643 < baseStart_8117643 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117657 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 1, 5, 2]
def baseStart_8117657 : Nat := 118140960795 + 8117657 * 2 ^ 59
def prefixEnd_8117657 : Nat := 4983230072969 + 3 ^ 40 * 8117657 * 2
def baseEnd_8117657 : Nat := 4168259829334851363355081

theorem tailTrace_8117657 : CollatzResearch.WordTrace tailWord_8117657 prefixEnd_8117657 4168259829334851363355081 := by
  unfold tailWord_8117657
  simp only [CollatzResearch.WordTrace]
  refine ⟨296075274352122549284927225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197383516234748366189951483 296075274352122549284927225)
  ·
    refine ⟨222056455764091911963695419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296075274352122549284927225 222056455764091911963695419)
    ·
      refine ⟨333084683646137867945543129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222056455764091911963695419 333084683646137867945543129)
      ·
        refine ⟨249813512734603400959157347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333084683646137867945543129 249813512734603400959157347)
        ·
          refine ⟨374720269101905101438736021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249813512734603400959157347 374720269101905101438736021)
          ·
            refine ⟨17565012614151801629940751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 374720269101905101438736021 17565012614151801629940751)
            ·
              refine ⟨26347518921227702444911127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17565012614151801629940751 26347518921227702444911127)
              ·
                refine ⟨39521278381841553667366691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26347518921227702444911127 39521278381841553667366691)
                ·
                  refine ⟨59281917572762330501050037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39521278381841553667366691 59281917572762330501050037)
                  ·
                    refine ⟨5557679772446468484473441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59281917572762330501050037 5557679772446468484473441)
                    ·
                      refine ⟨4168259829334851363355081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5557679772446468484473441 4168259829334851363355081)
                      ·
                        rfl

theorem cell23_8117657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 5, 2].length) (baseStart_8117657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117657 prefixEnd_8117657 := by exact prefixLift 8117657
  have htrace : WordTrace (prefixWord ++ tailWord_8117657) baseStart_8117657 baseEnd_8117657 := by
    simpa [prefixWord, tailWord_8117657, baseEnd_8117657] using wordTrace_append hprefix tailTrace_8117657
  have hstable : (prefixWord ++ tailWord_8117657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117657).length < 2 ^ (prefixWord ++ tailWord_8117657).sum := by decide
  have hdescent : baseEnd_8117657 < baseStart_8117657 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117704 : List Nat := [2, 1, 3, 1, 3, 1, 1, 4, 3, 2, 2]
def baseStart_8117704 : Nat := 118140960795 + 8117704 * 2 ^ 59
def prefixEnd_8117704 : Nat := 4983230072969 + 3 ^ 40 * 8117704 * 2
def baseEnd_8117704 : Nat := 4168283962925612679467365

theorem tailTrace_8117704 : CollatzResearch.WordTrace tailWord_8117704 prefixEnd_8117704 4168283962925612679467365 := by
  unfold tailWord_8117704
  simp only [CollatzResearch.WordTrace]
  refine ⟨148038494291476138155944083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197384659055301517541258777 148038494291476138155944083)
  ·
    refine ⟨222057741437214207233916125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148038494291476138155944083 222057741437214207233916125)
    ·
      refine ⟨83271653038955327712718547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222057741437214207233916125 83271653038955327712718547)
      ·
        refine ⟨124907479558432991569077821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83271653038955327712718547 124907479558432991569077821)
        ·
          refine ⟨46840304834412371838404183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124907479558432991569077821 46840304834412371838404183)
          ·
            refine ⟨70260457251618557757606275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46840304834412371838404183 70260457251618557757606275)
            ·
              refine ⟨105390685877427836636409413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70260457251618557757606275 105390685877427836636409413)
              ·
                refine ⟨19760753602017719369326765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105390685877427836636409413 19760753602017719369326765)
                ·
                  refine ⟨7410282600756644763497537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19760753602017719369326765 7410282600756644763497537)
                  ·
                    refine ⟨5557711950567483572623153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7410282600756644763497537 5557711950567483572623153)
                    ·
                      refine ⟨4168283962925612679467365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5557711950567483572623153 4168283962925612679467365)
                      ·
                        rfl

theorem cell23_8117704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_8117704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117704 prefixEnd_8117704 := by exact prefixLift 8117704
  have htrace : WordTrace (prefixWord ++ tailWord_8117704) baseStart_8117704 baseEnd_8117704 := by
    simpa [prefixWord, tailWord_8117704, baseEnd_8117704] using wordTrace_append hprefix tailTrace_8117704
  have hstable : (prefixWord ++ tailWord_8117704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117704).length < 2 ^ (prefixWord ++ tailWord_8117704).sum := by decide
  have hdescent : baseEnd_8117704 < baseStart_8117704 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117707 : List Nat := [1, 1, 1, 1, 3, 3, 3, 4, 1, 2, 3]
def baseStart_8117707 : Nat := 118140960795 + 8117707 * 2 ^ 59
def prefixEnd_8117707 : Nat := 4983230072969 + 3 ^ 40 * 8117707 * 2
def baseEnd_8117707 : Nat := 4168285503367576167729851

theorem tailTrace_8117707 : CollatzResearch.WordTrace tailWord_8117707 prefixEnd_8117707 4168285503367576167729851 := by
  unfold tailWord_8117707
  simp only [CollatzResearch.WordTrace]
  refine ⟨296077098001941407824247375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197384732001294271882831583 296077098001941407824247375)
  ·
    refine ⟨444115647002912111736371063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296077098001941407824247375 444115647002912111736371063)
    ·
      refine ⟨666173470504368167604556595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444115647002912111736371063 666173470504368167604556595)
      ·
        refine ⟨999260205756552251406834893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666173470504368167604556595 999260205756552251406834893)
        ·
          refine ⟨374722577158707094277563085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 999260205756552251406834893 374722577158707094277563085)
          ·
            refine ⟨140520966434515160354086157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374722577158707094277563085 140520966434515160354086157)
            ·
              refine ⟨52695362412943185132782309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140520966434515160354086157 52695362412943185132782309)
              ·
                refine ⟨9880380452426847212396683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52695362412943185132782309 9880380452426847212396683)
                ·
                  refine ⟨14820570678640270818595025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9880380452426847212396683 14820570678640270818595025)
                  ·
                    refine ⟨11115428008980203113946269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14820570678640270818595025 11115428008980203113946269)
                    ·
                      refine ⟨4168285503367576167729851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11115428008980203113946269 4168285503367576167729851)
                      ·
                        rfl

theorem cell23_8117707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 2, 3].length) (baseStart_8117707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117707 prefixEnd_8117707 := by exact prefixLift 8117707
  have htrace : WordTrace (prefixWord ++ tailWord_8117707) baseStart_8117707 baseEnd_8117707 := by
    simpa [prefixWord, tailWord_8117707, baseEnd_8117707] using wordTrace_append hprefix tailTrace_8117707
  have hstable : (prefixWord ++ tailWord_8117707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117707).length < 2 ^ (prefixWord ++ tailWord_8117707).sum := by decide
  have hdescent : baseEnd_8117707 < baseStart_8117707 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117738 : List Nat := [3, 1, 3, 1, 4, 2, 1, 1, 3, 2, 2]
def baseStart_8117738 : Nat := 118140960795 + 8117738 * 2 ^ 59
def prefixEnd_8117738 : Nat := 4983230072969 + 3 ^ 40 * 8117738 * 2
def baseEnd_8117738 : Nat := 4168301421267865546442209

theorem tailTrace_8117738 : CollatzResearch.WordTrace tailWord_8117738 prefixEnd_8117738 4168301421267865546442209 := by
  unfold tailWord_8117738
  simp only [CollatzResearch.WordTrace]
  refine ⟨74019557166207275029656467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197385485776552733412417245 74019557166207275029656467)
  ·
    refine ⟨111029335749310912544484701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74019557166207275029656467 111029335749310912544484701)
    ·
      refine ⟨41636000905991592204181763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111029335749310912544484701 41636000905991592204181763)
      ·
        refine ⟨62454001358987388306272645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41636000905991592204181763 62454001358987388306272645)
        ·
          refine ⟨11710125254810135307426121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62454001358987388306272645 11710125254810135307426121)
          ·
            refine ⟨8782593941107601480569591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11710125254810135307426121 8782593941107601480569591)
            ·
              refine ⟨13173890911661402220854387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8782593941107601480569591 13173890911661402220854387)
              ·
                refine ⟨19760836367492103331281581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13173890911661402220854387 19760836367492103331281581)
                ·
                  refine ⟨7410313637809538749230593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19760836367492103331281581 7410313637809538749230593)
                  ·
                    refine ⟨5557735228357154061922945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7410313637809538749230593 5557735228357154061922945)
                    ·
                      refine ⟨4168301421267865546442209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5557735228357154061922945 4168301421267865546442209)
                      ·
                        rfl

theorem cell23_8117738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_8117738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117738 prefixEnd_8117738 := by exact prefixLift 8117738
  have htrace : WordTrace (prefixWord ++ tailWord_8117738) baseStart_8117738 baseEnd_8117738 := by
    simpa [prefixWord, tailWord_8117738, baseEnd_8117738] using wordTrace_append hprefix tailTrace_8117738
  have hstable : (prefixWord ++ tailWord_8117738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117738).length < 2 ^ (prefixWord ++ tailWord_8117738).sum := by decide
  have hdescent : baseEnd_8117738 < baseStart_8117738 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117754 : List Nat := [3, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3]
def baseStart_8117754 : Nat := 118140960795 + 8117754 * 2 ^ 59
def prefixEnd_8117754 : Nat := 4983230072969 + 3 ^ 40 * 8117754 * 2
def baseEnd_8117754 : Nat := 4168309636958337483842135

theorem tailTrace_8117754 : CollatzResearch.WordTrace tailWord_8117754 prefixEnd_8117754 4168309636958337483842135 := by
  unfold tailWord_8117754
  simp only [CollatzResearch.WordTrace]
  refine ⟨74019703058192783712802079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197385874821847423234138877 74019703058192783712802079)
  ·
    refine ⟨111029554587289175569203119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74019703058192783712802079 111029554587289175569203119)
    ·
      refine ⟨166544331880933763353804679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111029554587289175569203119 166544331880933763353804679)
      ·
        refine ⟨249816497821400645030707019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166544331880933763353804679 249816497821400645030707019)
        ·
          refine ⟨374724746732100967546060529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249816497821400645030707019 374724746732100967546060529)
          ·
            refine ⟨281043560049075725659545397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374724746732100967546060529 281043560049075725659545397)
            ·
              refine ⟨26347833754600849280582381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 281043560049075725659545397 26347833754600849280582381)
              ·
                refine ⟨9880437657975318480218393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26347833754600849280582381 9880437657975318480218393)
                ·
                  refine ⟨7410328243481488860163795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9880437657975318480218393 7410328243481488860163795)
                  ·
                    refine ⟨11115492365222233290245693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7410328243481488860163795 11115492365222233290245693)
                    ·
                      refine ⟨4168309636958337483842135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11115492365222233290245693 4168309636958337483842135)
                      ·
                        rfl

theorem cell23_8117754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3].length) (baseStart_8117754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117754 prefixEnd_8117754 := by exact prefixLift 8117754
  have htrace : WordTrace (prefixWord ++ tailWord_8117754) baseStart_8117754 baseEnd_8117754 := by
    simpa [prefixWord, tailWord_8117754, baseEnd_8117754] using wordTrace_append hprefix tailTrace_8117754
  have hstable : (prefixWord ++ tailWord_8117754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117754).length < 2 ^ (prefixWord ++ tailWord_8117754).sum := by decide
  have hdescent : baseEnd_8117754 < baseStart_8117754 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117811 : List Nat := [1, 1, 1, 2, 4, 3, 2, 3, 2, 2, 2]
def baseStart_8117811 : Nat := 118140960795 + 8117811 * 2 ^ 59
def prefixEnd_8117811 : Nat := 4983230072969 + 3 ^ 40 * 8117811 * 2
def baseEnd_8117811 : Nat := 4168338905355643760829373

theorem tailTrace_8117811 : CollatzResearch.WordTrace tailWord_8117811 prefixEnd_8117811 4168338905355643760829373 := by
  unfold tailWord_8117811
  simp only [CollatzResearch.WordTrace]
  refine ⟨296080891193564633586033287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197387260795709755724022191 296080891193564633586033287)
  ·
    refine ⟨444121336790346950379049931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296080891193564633586033287 444121336790346950379049931)
    ·
      refine ⟨666182005185520425568574897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444121336790346950379049931 666182005185520425568574897)
      ·
        refine ⟨499636503889140319176431173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666182005185520425568574897 499636503889140319176431173)
        ·
          refine ⟨93681844479213809845580845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 499636503889140319176431173 93681844479213809845580845)
          ·
            refine ⟨35130691679705178692092817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93681844479213809845580845 35130691679705178692092817)
            ·
              refine ⟨26348018759778884019069613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35130691679705178692092817 26348018759778884019069613)
              ·
                refine ⟨9880507034917081507151105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26348018759778884019069613 9880507034917081507151105)
                ·
                  refine ⟨7410380276187811130363329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9880507034917081507151105 7410380276187811130363329)
                  ·
                    refine ⟨5557785207140858347772497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7410380276187811130363329 5557785207140858347772497)
                    ·
                      refine ⟨4168338905355643760829373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5557785207140858347772497 4168338905355643760829373)
                      ·
                        rfl

theorem cell23_8117811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 2, 2].length) (baseStart_8117811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117811 prefixEnd_8117811 := by exact prefixLift 8117811
  have htrace : WordTrace (prefixWord ++ tailWord_8117811) baseStart_8117811 baseEnd_8117811 := by
    simpa [prefixWord, tailWord_8117811, baseEnd_8117811] using wordTrace_append hprefix tailTrace_8117811
  have hstable : (prefixWord ++ tailWord_8117811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117811).length < 2 ^ (prefixWord ++ tailWord_8117811).sum := by decide
  have hdescent : baseEnd_8117811 < baseStart_8117811 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117817 : List Nat := [1, 2, 1, 5, 1, 3, 1, 2, 7]
def baseStart_8117817 : Nat := 118140960795 + 8117817 * 2 ^ 59
def prefixEnd_8117817 : Nat := 4983230072969 + 3 ^ 40 * 8117817 * 2
def baseEnd_8117817 : Nat := 463149109582174526372705

theorem tailTrace_8117817 : CollatzResearch.WordTrace tailWord_8117817 prefixEnd_8117817 463149109582174526372705 := by
  unfold tailWord_8117817
  simp only [CollatzResearch.WordTrace]
  refine ⟨296081110031542896610751705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197387406687695264407167803 296081110031542896610751705)
  ·
    refine ⟨222060832523657172458063779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296081110031542896610751705 222060832523657172458063779)
    ·
      refine ⟨333091248785485758687095669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222060832523657172458063779 333091248785485758687095669)
      ·
        refine ⟨31227304573639289876915219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 333091248785485758687095669 31227304573639289876915219)
        ·
          refine ⟨46840956860458934815372829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31227304573639289876915219 46840956860458934815372829)
          ·
            refine ⟨17565358822672100555764811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46840956860458934815372829 17565358822672100555764811)
            ·
              refine ⟨26348038234008150833647217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17565358822672100555764811 26348038234008150833647217)
              ·
                refine ⟨19761028675506113125235413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26348038234008150833647217 19761028675506113125235413)
                ·
                  refine ⟨463149109582174526372705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19761028675506113125235413 463149109582174526372705)
                  ·
                    rfl

theorem cell23_8117817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 7].length) (baseStart_8117817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117817 prefixEnd_8117817 := by exact prefixLift 8117817
  have htrace : WordTrace (prefixWord ++ tailWord_8117817) baseStart_8117817 baseEnd_8117817 := by
    simpa [prefixWord, tailWord_8117817, baseEnd_8117817] using wordTrace_append hprefix tailTrace_8117817
  have hstable : (prefixWord ++ tailWord_8117817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117817).length < 2 ^ (prefixWord ++ tailWord_8117817).sum := by decide
  have hdescent : baseEnd_8117817 < baseStart_8117817 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117834 : List Nat := [3, 1, 2, 1, 1, 3, 4, 3, 5]
def baseStart_8117834 : Nat := 118140960795 + 8117834 * 2 ^ 59
def prefixEnd_8117834 : Nat := 4983230072969 + 3 ^ 40 * 8117834 * 2
def baseEnd_8117834 : Nat := 463150079490077463426863

theorem tailTrace_8117834 : CollatzResearch.WordTrace tailWord_8117834 prefixEnd_8117834 463150079490077463426863 := by
  unfold tailWord_8117834
  simp only [CollatzResearch.WordTrace]
  refine ⟨74020432518120327128530139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197387820048320872342747037 74020432518120327128530139)
  ·
    refine ⟨111030648777180490692795209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74020432518120327128530139 111030648777180490692795209)
    ·
      refine ⟨83272986582885368019596407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111030648777180490692795209 83272986582885368019596407)
      ·
        refine ⟨124909479874328052029394611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83272986582885368019596407 124909479874328052029394611)
        ·
          refine ⟨187364219811492078044091917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124909479874328052029394611 187364219811492078044091917)
          ·
            refine ⟨70261582429309529266534469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187364219811492078044091917 70261582429309529266534469)
            ·
              refine ⟨13174046705495536737475213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70261582429309529266534469 13174046705495536737475213)
              ·
                refine ⟨4940267514560826276553205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13174046705495536737475213 4940267514560826276553205)
                ·
                  refine ⟨463150079490077463426863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4940267514560826276553205 463150079490077463426863)
                  ·
                    rfl

theorem cell23_8117834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 5].length) (baseStart_8117834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117834 prefixEnd_8117834 := by exact prefixLift 8117834
  have htrace : WordTrace (prefixWord ++ tailWord_8117834) baseStart_8117834 baseEnd_8117834 := by
    simpa [prefixWord, tailWord_8117834, baseEnd_8117834] using wordTrace_append hprefix tailTrace_8117834
  have hstable : (prefixWord ++ tailWord_8117834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117834).length < 2 ^ (prefixWord ++ tailWord_8117834).sum := by decide
  have hdescent : baseEnd_8117834 < baseStart_8117834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117911 : List Nat := [1, 1, 3, 3, 2, 4, 1, 1, 3, 4]
def baseStart_8117911 : Nat := 118140960795 + 8117911 * 2 ^ 59
def prefixEnd_8117911 : Nat := 4983230072969 + 3 ^ 40 * 8117911 * 2
def baseEnd_8117911 : Nat := 1389463417807031123192971

theorem tailTrace_8117911 : CollatzResearch.WordTrace tailWord_8117911 prefixEnd_8117911 1389463417807031123192971 := by
  unfold tailWord_8117911
  simp only [CollatzResearch.WordTrace]
  refine ⟨296084538493202350664673587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197389692328801567109782391 296084538493202350664673587)
  ·
    refine ⟨444126807739803525997010381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296084538493202350664673587 444126807739803525997010381)
    ·
      refine ⟨166547552902426322248878893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444126807739803525997010381 166547552902426322248878893)
      ·
        refine ⟨62455332338409870843329585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166547552902426322248878893 62455332338409870843329585)
        ·
          refine ⟨46841499253807403132497189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62455332338409870843329585 46841499253807403132497189)
          ·
            refine ⟨8782781110088888087343223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46841499253807403132497189 8782781110088888087343223)
            ·
              refine ⟨13174171665133332131014835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8782781110088888087343223 13174171665133332131014835)
              ·
                refine ⟨19761257497699998196522253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13174171665133332131014835 19761257497699998196522253)
                ·
                  refine ⟨7410471561637499323695845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19761257497699998196522253 7410471561637499323695845)
                  ·
                    refine ⟨1389463417807031123192971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7410471561637499323695845 1389463417807031123192971)
                    ·
                      rfl

theorem cell23_8117911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_8117911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117911 prefixEnd_8117911 := by exact prefixLift 8117911
  have htrace : WordTrace (prefixWord ++ tailWord_8117911) baseStart_8117911 baseEnd_8117911 := by
    simpa [prefixWord, tailWord_8117911, baseEnd_8117911] using wordTrace_append hprefix tailTrace_8117911
  have hstable : (prefixWord ++ tailWord_8117911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117911).length < 2 ^ (prefixWord ++ tailWord_8117911).sum := by decide
  have hdescent : baseEnd_8117911 < baseStart_8117911 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117924 : List Nat := [2, 3, 1, 2, 2, 3, 1, 3, 6]
def baseStart_8117924 : Nat := 118140960795 + 8117924 * 2 ^ 59
def prefixEnd_8117924 : Nat := 4983230072969 + 3 ^ 40 * 8117924 * 2
def baseEnd_8117924 : Nat := 463155214296622424301817

theorem tailTrace_8117924 : CollatzResearch.WordTrace tailWord_8117924 prefixEnd_8117924 463155214296622424301817 := by
  unfold tailWord_8117924
  simp only [CollatzResearch.WordTrace]
  refine ⟨148042506321077626942448413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197390008428103502589931217 148042506321077626942448413)
  ·
    refine ⟨55515939870404110103418155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148042506321077626942448413 55515939870404110103418155)
    ·
      refine ⟨83273909805606165155127233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55515939870404110103418155 83273909805606165155127233)
      ·
        refine ⟨62455432354204623866345425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83273909805606165155127233 62455432354204623866345425)
        ·
          refine ⟨46841574265653467899759069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62455432354204623866345425 46841574265653467899759069)
          ·
            refine ⟨17565590349620050462409651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46841574265653467899759069 17565590349620050462409651)
            ·
              refine ⟨26348385524430075693614477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17565590349620050462409651 26348385524430075693614477)
              ·
                refine ⟨9880644571661278385105429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26348385524430075693614477 9880644571661278385105429)
                ·
                  refine ⟨463155214296622424301817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9880644571661278385105429 463155214296622424301817)
                  ·
                    rfl

theorem cell23_8117924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_8117924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117924 prefixEnd_8117924 := by exact prefixLift 8117924
  have htrace : WordTrace (prefixWord ++ tailWord_8117924) baseStart_8117924 baseEnd_8117924 := by
    simpa [prefixWord, tailWord_8117924, baseEnd_8117924] using wordTrace_append hprefix tailTrace_8117924
  have hstable : (prefixWord ++ tailWord_8117924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117924).length < 2 ^ (prefixWord ++ tailWord_8117924).sum := by decide
  have hdescent : baseEnd_8117924 < baseStart_8117924 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117944 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 1, 5, 2]
def baseStart_8117944 : Nat := 118140960795 + 8117944 * 2 ^ 59
def prefixEnd_8117944 : Nat := 4983230072969 + 3 ^ 40 * 8117944 * 2
def baseEnd_8117944 : Nat := 4168407198282691740466261

theorem tailTrace_8117944 : CollatzResearch.WordTrace tailWord_8117944 prefixEnd_8117944 4168407198282691740466261 := by
  unfold tailWord_8117944
  simp only [CollatzResearch.WordTrace]
  refine ⟨148042871051041398650312443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197390494734721864867083257 148042871051041398650312443)
  ·
    refine ⟨222064306576562097975468665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148042871051041398650312443 222064306576562097975468665)
    ·
      refine ⟨166548229932421573481601499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222064306576562097975468665 166548229932421573481601499)
      ·
        refine ⟨249822344898632360222402249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166548229932421573481601499 249822344898632360222402249)
        ·
          refine ⟨187366758673974270166801687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249822344898632360222402249 187366758673974270166801687)
          ·
            refine ⟨281050138010961405250202531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187366758673974270166801687 281050138010961405250202531)
            ·
              refine ⟨421575207016442107875303797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281050138010961405250202531 421575207016442107875303797)
              ·
                refine ⟨39522675657791447613309731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 421575207016442107875303797 39522675657791447613309731)
                ·
                  refine ⟨59284013486687171419964597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39522675657791447613309731 59284013486687171419964597)
                  ·
                    refine ⟨5557876264376922320621681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59284013486687171419964597 5557876264376922320621681)
                    ·
                      refine ⟨4168407198282691740466261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5557876264376922320621681 4168407198282691740466261)
                      ·
                        rfl

theorem cell23_8117944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 1, 5, 2].length) (baseStart_8117944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117944 prefixEnd_8117944 := by exact prefixLift 8117944
  have htrace : WordTrace (prefixWord ++ tailWord_8117944) baseStart_8117944 baseEnd_8117944 := by
    simpa [prefixWord, tailWord_8117944, baseEnd_8117944] using wordTrace_append hprefix tailTrace_8117944
  have hstable : (prefixWord ++ tailWord_8117944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117944).length < 2 ^ (prefixWord ++ tailWord_8117944).sum := by decide
  have hdescent : baseEnd_8117944 < baseStart_8117944 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117958 : List Nat := [6, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_8117958 : Nat := 118140960795 + 8117958 * 2 ^ 59
def prefixEnd_8117958 : Nat := 4983230072969 + 3 ^ 40 * 8117958 * 2
def baseEnd_8117958 : Nat := 463157154112428298410133

theorem tailTrace_8117958 : CollatzResearch.WordTrace tailWord_8117958 prefixEnd_8117958 463157154112428298410133 := by
  unfold tailWord_8117958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9252695397626002427863579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 197390835149354718461089685 9252695397626002427863579)
  ·
    refine ⟨13879043096439003641795369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9252695397626002427863579 13879043096439003641795369)
    ·
      refine ⟨10409282322329252731346527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13879043096439003641795369 10409282322329252731346527)
      ·
        refine ⟨15613923483493879097019791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10409282322329252731346527 15613923483493879097019791)
        ·
          refine ⟨23420885225240818645529687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15613923483493879097019791 23420885225240818645529687)
          ·
            refine ⟨35131327837861227968294531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23420885225240818645529687 35131327837861227968294531)
            ·
              refine ⟨52696991756791841952441797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35131327837861227968294531 52696991756791841952441797)
              ·
                refine ⟨9880685954398470366082837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52696991756791841952441797 9880685954398470366082837)
                ·
                  refine ⟨463157154112428298410133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9880685954398470366082837 463157154112428298410133)
                  ·
                    rfl

theorem cell23_8117958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_8117958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117958 prefixEnd_8117958 := by exact prefixLift 8117958
  have htrace : WordTrace (prefixWord ++ tailWord_8117958) baseStart_8117958 baseEnd_8117958 := by
    simpa [prefixWord, tailWord_8117958, baseEnd_8117958] using wordTrace_append hprefix tailTrace_8117958
  have hstable : (prefixWord ++ tailWord_8117958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117958).length < 2 ^ (prefixWord ++ tailWord_8117958).sum := by decide
  have hdescent : baseEnd_8117958 < baseStart_8117958 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8117962 : List Nat := [3, 1, 2, 1, 6, 1, 2, 2, 1, 4]
def baseStart_8117962 : Nat := 118140960795 + 8117962 * 2 ^ 59
def prefixEnd_8117962 : Nat := 4983230072969 + 3 ^ 40 * 8117962 * 2
def baseEnd_8117962 : Nat := 1389472146978157556680393

theorem tailTrace_8117962 : CollatzResearch.WordTrace tailWord_8117962 prefixEnd_8117962 1389472146978157556680393 := by
  unfold tailWord_8117962
  simp only [CollatzResearch.WordTrace]
  refine ⟨74021599654004396593695035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197390932410678390916520093 74021599654004396593695035)
  ·
    refine ⟨111032399481006594890542553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74021599654004396593695035 111032399481006594890542553)
    ·
      refine ⟨83274299610754946167906915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111032399481006594890542553 83274299610754946167906915)
      ·
        refine ⟨124911449416132419251860373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83274299610754946167906915 124911449416132419251860373)
        ·
          refine ⟨5855224191381207152430955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 124911449416132419251860373 5855224191381207152430955)
          ·
            refine ⟨8782836287071810728646433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5855224191381207152430955 8782836287071810728646433)
            ·
              refine ⟨6587127215303858046484825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8782836287071810728646433 6587127215303858046484825)
              ·
                refine ⟨4940345411477893534863619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6587127215303858046484825 4940345411477893534863619)
                ·
                  refine ⟨7410518117216840302295429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4940345411477893534863619 7410518117216840302295429)
                  ·
                    refine ⟨1389472146978157556680393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7410518117216840302295429 1389472146978157556680393)
                    ·
                      rfl

theorem cell23_8117962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_8117962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8117962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8117962 prefixEnd_8117962 := by exact prefixLift 8117962
  have htrace : WordTrace (prefixWord ++ tailWord_8117962) baseStart_8117962 baseEnd_8117962 := by
    simpa [prefixWord, tailWord_8117962, baseEnd_8117962] using wordTrace_append hprefix tailTrace_8117962
  have hstable : (prefixWord ++ tailWord_8117962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8117962).length < 2 ^ (prefixWord ++ tailWord_8117962).sum := by decide
  have hdescent : baseEnd_8117962 < baseStart_8117962 := by decide
  rcases family_descends (prefixWord ++ tailWord_8117962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118027 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 1, 9]
def baseStart_8118027 : Nat := 118140960795 + 8118027 * 2 ^ 59
def prefixEnd_8118027 : Nat := 4983230072969 + 3 ^ 40 * 8118027 * 2
def baseEnd_8118027 : Nat := 1389483272392338305242793

theorem tailTrace_8118027 : CollatzResearch.WordTrace tailWord_8118027 prefixEnd_8118027 1389483272392338305242793 := by
  unfold tailWord_8118027
  simp only [CollatzResearch.WordTrace]
  refine ⟨296088769360782102475896335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197392512907188068317264223 296088769360782102475896335)
  ·
    refine ⟨444133154041173153713844503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296088769360782102475896335 444133154041173153713844503)
    ·
      refine ⟨666199731061759730570766755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444133154041173153713844503 666199731061759730570766755)
      ·
        refine ⟨999299596592639595856150133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666199731061759730570766755 999299596592639595856150133)
        ·
          refine ⟨93684337180559962111514075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 999299596592639595856150133 93684337180559962111514075)
          ·
            refine ⟨140526505770839943167271113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93684337180559962111514075 140526505770839943167271113)
            ·
              refine ⟨105394879328129957375453335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140526505770839943167271113 105394879328129957375453335)
              ·
                refine ⟨158092318992194936063180003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105394879328129957375453335 158092318992194936063180003)
                ·
                  refine ⟨237138478488292404094770005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158092318992194936063180003 237138478488292404094770005)
                  ·
                    refine ⟨1389483272392338305242793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 237138478488292404094770005 1389483272392338305242793)
                    ·
                      rfl

theorem cell23_8118027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 9].length) (baseStart_8118027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118027 prefixEnd_8118027 := by exact prefixLift 8118027
  have htrace : WordTrace (prefixWord ++ tailWord_8118027) baseStart_8118027 baseEnd_8118027 := by
    simpa [prefixWord, tailWord_8118027, baseEnd_8118027] using wordTrace_append hprefix tailTrace_8118027
  have hstable : (prefixWord ++ tailWord_8118027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118027).length < 2 ^ (prefixWord ++ tailWord_8118027).sum := by decide
  have hdescent : baseEnd_8118027 < baseStart_8118027 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118051 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 3, 3, 2]
def baseStart_8118051 : Nat := 118140960795 + 8118051 * 2 ^ 59
def prefixEnd_8118051 : Nat := 4983230072969 + 3 ^ 40 * 8118051 * 2
def baseEnd_8118051 : Nat := 4168462140712722821828269

theorem tailTrace_8118051 : CollatzResearch.WordTrace tailWord_8118051 prefixEnd_8118051 4168462140712722821828269 := by
  unfold tailWord_8118051
  simp only [CollatzResearch.WordTrace]
  refine ⟨296089644712695154574770007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197393096475130103049846671 296089644712695154574770007)
  ·
    refine ⟨444134467069042731862155011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296089644712695154574770007 444134467069042731862155011)
    ·
      refine ⟨666201700603564097793232517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444134467069042731862155011 666201700603564097793232517)
      ·
        refine ⟨124912818863168268336231097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 666201700603564097793232517 124912818863168268336231097)
        ·
          refine ⟨93684614147376201252173323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124912818863168268336231097 93684614147376201252173323)
          ·
            refine ⟨140526921221064301878259985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93684614147376201252173323 140526921221064301878259985)
            ·
              refine ⟨105395190915798226408694989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140526921221064301878259985 105395190915798226408694989)
              ·
                refine ⟨39523196593424334903260621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105395190915798226408694989 39523196593424334903260621)
                ·
                  refine ⟨14821198722534125588722733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39523196593424334903260621 14821198722534125588722733)
                  ·
                    refine ⟨5557949520950297095771025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14821198722534125588722733 5557949520950297095771025)
                    ·
                      refine ⟨4168462140712722821828269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5557949520950297095771025 4168462140712722821828269)
                      ·
                        rfl

theorem cell23_8118051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_8118051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118051 prefixEnd_8118051 := by exact prefixLift 8118051
  have htrace : WordTrace (prefixWord ++ tailWord_8118051) baseStart_8118051 baseEnd_8118051 := by
    simpa [prefixWord, tailWord_8118051, baseEnd_8118051] using wordTrace_append hprefix tailTrace_8118051
  have hstable : (prefixWord ++ tailWord_8118051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118051).length < 2 ^ (prefixWord ++ tailWord_8118051).sum := by decide
  have hdescent : baseEnd_8118051 < baseStart_8118051 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118092 : List Nat := [2, 2, 1, 3, 4, 2, 2, 1, 2, 1, 3]
def baseStart_8118092 : Nat := 118140960795 + 8118092 * 2 ^ 59
def prefixEnd_8118092 : Nat := 4983230072969 + 3 ^ 40 * 8118092 * 2
def baseEnd_8118092 : Nat := 4168483193419557161415581

theorem tailTrace_8118092 : CollatzResearch.WordTrace tailWord_8118092 prefixEnd_8118092 4168483193419557161415581 := by
  unfold tailWord_8118092
  simp only [CollatzResearch.WordTrace]
  refine ⟨148045570052773309288506265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197394093403697745718008353 148045570052773309288506265)
  ·
    refine ⟨111034177539579981966379699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148045570052773309288506265 111034177539579981966379699)
    ·
      refine ⟨166551266309369972949569549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111034177539579981966379699 166551266309369972949569549)
      ·
        refine ⟨62456724866013739856088581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166551266309369972949569549 62456724866013739856088581)
        ·
          refine ⟨11710635912377576223016609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62456724866013739856088581 11710635912377576223016609)
          ·
            refine ⟨8782976934283182167262457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11710635912377576223016609 8782976934283182167262457)
            ·
              refine ⟨6587232700712386625446843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8782976934283182167262457 6587232700712386625446843)
              ·
                refine ⟨9880849051068579938170265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6587232700712386625446843 9880849051068579938170265)
                ·
                  refine ⟨7410636788301434953627699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9880849051068579938170265 7410636788301434953627699)
                  ·
                    refine ⟨11115955182452152430441549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7410636788301434953627699 11115955182452152430441549)
                    ·
                      refine ⟨4168483193419557161415581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11115955182452152430441549 4168483193419557161415581)
                      ·
                        rfl

theorem cell23_8118092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_8118092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118092 prefixEnd_8118092 := by exact prefixLift 8118092
  have htrace : WordTrace (prefixWord ++ tailWord_8118092) baseStart_8118092 baseEnd_8118092 := by
    simpa [prefixWord, tailWord_8118092, baseEnd_8118092] using wordTrace_append hprefix tailTrace_8118092
  have hstable : (prefixWord ++ tailWord_8118092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118092).length < 2 ^ (prefixWord ++ tailWord_8118092).sum := by decide
  have hdescent : baseEnd_8118092 < baseStart_8118092 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118138 : List Nat := [3, 1, 1, 1, 1, 1, 8, 2, 5]
def baseStart_8118138 : Nat := 118140960795 + 8118138 * 2 ^ 59
def prefixEnd_8118138 : Nat := 4983230072969 + 3 ^ 40 * 8118138 * 2
def baseEnd_8118138 : Nat := 463167423725518220160041

theorem tailTrace_8118138 : CollatzResearch.WordTrace tailWord_8118138 prefixEnd_8118138 463167423725518220160041 := by
  unfold tailWord_8118138
  simp only [CollatzResearch.WordTrace]
  refine ⟨74023204465844992108296767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197395211908919978955458045 74023204465844992108296767)
  ·
    refine ⟨111034806698767488162445151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74023204465844992108296767 111034806698767488162445151)
    ·
      refine ⟨166552210048151232243667727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111034806698767488162445151 166552210048151232243667727)
      ·
        refine ⟨249828315072226848365501591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166552210048151232243667727 249828315072226848365501591)
        ·
          refine ⟨374742472608340272548252387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249828315072226848365501591 374742472608340272548252387)
          ·
            refine ⟨562113708912510408822378581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374742472608340272548252387 562113708912510408822378581)
            ·
              refine ⟨6587270026318481353387249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 562113708912510408822378581 6587270026318481353387249)
              ·
                refine ⟨4940452519738861015040437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6587270026318481353387249 4940452519738861015040437)
                ·
                  refine ⟨463167423725518220160041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4940452519738861015040437 463167423725518220160041)
                  ·
                    rfl

theorem cell23_8118138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 5].length) (baseStart_8118138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118138 prefixEnd_8118138 := by exact prefixLift 8118138
  have htrace : WordTrace (prefixWord ++ tailWord_8118138) baseStart_8118138 baseEnd_8118138 := by
    simpa [prefixWord, tailWord_8118138, baseEnd_8118138] using wordTrace_append hprefix tailTrace_8118138
  have hstable : (prefixWord ++ tailWord_8118138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118138).length < 2 ^ (prefixWord ++ tailWord_8118138).sum := by decide
  have hdescent : baseEnd_8118138 < baseStart_8118138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118144 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 5]
def baseStart_8118144 : Nat := 118140960795 + 8118144 * 2 ^ 59
def prefixEnd_8118144 : Nat := 4983230072969 + 3 ^ 40 * 8118144 * 2
def baseEnd_8118144 : Nat := 4168509894413590957965341

theorem tailTrace_8118144 : CollatzResearch.WordTrace tailWord_8118144 prefixEnd_8118144 4168509894413590957965341 := by
  unfold tailWord_8118144
  simp only [CollatzResearch.WordTrace]
  refine ⟨148046518350679115728952743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197395357800905487638603657 148046518350679115728952743)
  ·
    refine ⟨222069777526018673593429115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148046518350679115728952743 222069777526018673593429115)
    ·
      refine ⟨333104666289028010390143673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222069777526018673593429115 333104666289028010390143673)
      ·
        refine ⟨249828499716771007792607755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333104666289028010390143673 249828499716771007792607755)
        ·
          refine ⟨374742749575156511688911633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249828499716771007792607755 374742749575156511688911633)
          ·
            refine ⟨281057062181367383766683725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374742749575156511688911633 281057062181367383766683725)
            ·
              refine ⟨105396398318012768912506397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281057062181367383766683725 105396398318012768912506397)
              ·
                refine ⟨39523649369254788342189899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105396398318012768912506397 39523649369254788342189899)
                ·
                  refine ⟨59285474053882182513284849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39523649369254788342189899 59285474053882182513284849)
                  ·
                    refine ⟨44464105540411636884963637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59285474053882182513284849 44464105540411636884963637)
                    ·
                      refine ⟨4168509894413590957965341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44464105540411636884963637 4168509894413590957965341)
                      ·
                        rfl

theorem cell23_8118144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_8118144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118144 prefixEnd_8118144 := by exact prefixLift 8118144
  have htrace : WordTrace (prefixWord ++ tailWord_8118144) baseStart_8118144 baseEnd_8118144 := by
    simpa [prefixWord, tailWord_8118144, baseEnd_8118144] using wordTrace_append hprefix tailTrace_8118144
  have hstable : (prefixWord ++ tailWord_8118144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118144).length < 2 ^ (prefixWord ++ tailWord_8118144).sum := by decide
  have hdescent : baseEnd_8118144 < baseStart_8118144 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118168 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 1, 7]
def baseStart_8118168 : Nat := 118140960795 + 8118168 * 2 ^ 59
def prefixEnd_8118168 : Nat := 4983230072969 + 3 ^ 40 * 8118168 * 2
def baseEnd_8118168 : Nat := 1389507405983099621355077

theorem tailTrace_8118168 : CollatzResearch.WordTrace tailWord_8118168 prefixEnd_8118168 1389507405983099621355077 := by
  unfold tailWord_8118168
  simp only [CollatzResearch.WordTrace]
  refine ⟨148046956026635641778389579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197395941368847522371186105 148046956026635641778389579)
  ·
    refine ⟨222070434039953462667584369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148046956026635641778389579 222070434039953462667584369)
    ·
      refine ⟨166552825529965097000688277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222070434039953462667584369 166552825529965097000688277)
      ·
        refine ⟨7807163696717113921907263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 166552825529965097000688277 7807163696717113921907263)
        ·
          refine ⟨11710745545075670882860895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7807163696717113921907263 11710745545075670882860895)
          ·
            refine ⟨17566118317613506324291343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11710745545075670882860895 17566118317613506324291343)
            ·
              refine ⟨26349177476420259486437015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17566118317613506324291343 26349177476420259486437015)
              ·
                refine ⟨39523766214630389229655523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26349177476420259486437015 39523766214630389229655523)
                ·
                  refine ⟨59285649321945583844483285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39523766214630389229655523 59285649321945583844483285)
                  ·
                    refine ⟨1389507405983099621355077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59285649321945583844483285 1389507405983099621355077)
                    ·
                      rfl

theorem cell23_8118168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_8118168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118168 prefixEnd_8118168 := by exact prefixLift 8118168
  have htrace : WordTrace (prefixWord ++ tailWord_8118168) baseStart_8118168 baseEnd_8118168 := by
    simpa [prefixWord, tailWord_8118168, baseEnd_8118168] using wordTrace_append hprefix tailTrace_8118168
  have hstable : (prefixWord ++ tailWord_8118168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118168).length < 2 ^ (prefixWord ++ tailWord_8118168).sum := by decide
  have hdescent : baseEnd_8118168 < baseStart_8118168 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118191 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 3]
def baseStart_8118191 : Nat := 118140960795 + 8118191 * 2 ^ 59
def prefixEnd_8118191 : Nat := 4983230072969 + 3 ^ 40 * 8118191 * 2
def baseEnd_8118191 : Nat := 4168534028004352274077625

theorem tailTrace_8118191 : CollatzResearch.WordTrace tailWord_8118191 prefixEnd_8118191 4168534028004352274077625 := by
  unfold tailWord_8118191
  simp only [CollatzResearch.WordTrace]
  refine ⟨296094750932187958484866427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197396500621458638989910951 296094750932187958484866427)
  ·
    refine ⟨444142126398281937727299641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296094750932187958484866427 444142126398281937727299641)
    ·
      refine ⟨333106594798711453295474731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444142126398281937727299641 333106594798711453295474731)
      ·
        refine ⟨499659892198067179943212097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333106594798711453295474731 499659892198067179943212097)
        ·
          refine ⟨374744919148550384957409073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499659892198067179943212097 374744919148550384957409073)
          ·
            refine ⟨281058689361412788718056805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374744919148550384957409073 281058689361412788718056805)
            ·
              refine ⟨52698504255264897884635651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281058689361412788718056805 52698504255264897884635651)
              ·
                refine ⟨79047756382897346826953477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52698504255264897884635651 79047756382897346826953477)
                ·
                  refine ⟨14821454321793252530053777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79047756382897346826953477 14821454321793252530053777)
                  ·
                    refine ⟨11116090741344939397540333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14821454321793252530053777 11116090741344939397540333)
                    ·
                      refine ⟨4168534028004352274077625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11116090741344939397540333 4168534028004352274077625)
                      ·
                        rfl

theorem cell23_8118191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 3].length) (baseStart_8118191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118191 prefixEnd_8118191 := by exact prefixLift 8118191
  have htrace : WordTrace (prefixWord ++ tailWord_8118191) baseStart_8118191 baseEnd_8118191 := by
    simpa [prefixWord, tailWord_8118191, baseEnd_8118191] using wordTrace_append hprefix tailTrace_8118191
  have hstable : (prefixWord ++ tailWord_8118191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118191).length < 2 ^ (prefixWord ++ tailWord_8118191).sum := by decide
  have hdescent : baseEnd_8118191 < baseStart_8118191 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118242 : List Nat := [3, 3, 3, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_8118242 : Nat := 118140960795 + 8118242 * 2 ^ 59
def prefixEnd_8118242 : Nat := 4983230072969 + 3 ^ 40 * 8118242 * 2
def baseEnd_8118242 : Nat := 4168560215517731574539891

theorem tailTrace_8118242 : CollatzResearch.WordTrace tailWord_8118242 prefixEnd_8118242 4168560215517731574539891 := by
  unfold tailWord_8118242
  simp only [CollatzResearch.WordTrace]
  refine ⟨74024152763750798548743245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197397740703335462796648653 74024152763750798548743245)
  ·
    refine ⟨27759057286406549455778717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74024152763750798548743245 27759057286406549455778717)
    ·
      refine ⟨10409646482402456045917019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27759057286406549455778717 10409646482402456045917019)
      ·
        refine ⟨15614469723603684068875529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10409646482402456045917019 15614469723603684068875529)
        ·
          refine ⟨11710852292702763051656647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15614469723603684068875529 11710852292702763051656647)
          ·
            refine ⟨17566278439054144577484971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11710852292702763051656647 17566278439054144577484971)
            ·
              refine ⟨26349417658581216866227457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17566278439054144577484971 26349417658581216866227457)
              ·
                refine ⟨19762063243935912649670593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26349417658581216866227457 19762063243935912649670593)
                ·
                  refine ⟨14821547432951934487252945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19762063243935912649670593 14821547432951934487252945)
                  ·
                    refine ⟨11116160574713950865439709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14821547432951934487252945 11116160574713950865439709)
                    ·
                      refine ⟨4168560215517731574539891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11116160574713950865439709 4168560215517731574539891)
                      ·
                        rfl

theorem cell23_8118242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_8118242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118242 prefixEnd_8118242 := by exact prefixLift 8118242
  have htrace : WordTrace (prefixWord ++ tailWord_8118242) baseStart_8118242 baseEnd_8118242 := by
    simpa [prefixWord, tailWord_8118242, baseEnd_8118242] using wordTrace_append hprefix tailTrace_8118242
  have hstable : (prefixWord ++ tailWord_8118242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118242).length < 2 ^ (prefixWord ++ tailWord_8118242).sum := by decide
  have hdescent : baseEnd_8118242 < baseStart_8118242 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118262 : List Nat := [5, 1, 1, 1, 4, 2, 2, 1, 6]
def baseStart_8118262 : Nat := 118140960795 + 8118262 * 2 ^ 59
def prefixEnd_8118262 : Nat := 4983230072969 + 3 ^ 40 * 8118262 * 2
def baseEnd_8118262 : Nat := 463174498347869055143311

theorem tailTrace_8118262 : CollatzResearch.WordTrace tailWord_8118262 prefixEnd_8118262 463174498347869055143311 := by
  unfold tailWord_8118262
  simp only [CollatzResearch.WordTrace]
  refine ⟨18506083782183171100668815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197398227009953825073800693 18506083782183171100668815)
  ·
    refine ⟨27759125673274756651003223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18506083782183171100668815 27759125673274756651003223)
    ·
      refine ⟨41638688509912134976504835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27759125673274756651003223 41638688509912134976504835)
      ·
        refine ⟨62458032764868202464757253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41638688509912134976504835 62458032764868202464757253)
        ·
          refine ⟨11710881143412787962141985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62458032764868202464757253 11710881143412787962141985)
          ·
            refine ⟨8783160857559590971606489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11710881143412787962141985 8783160857559590971606489)
            ·
              refine ⟨6587370643169693228704867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8783160857559590971606489 6587370643169693228704867)
              ·
                refine ⟨9881055964754539843057301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6587370643169693228704867 9881055964754539843057301)
                ·
                  refine ⟨463174498347869055143311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9881055964754539843057301 463174498347869055143311)
                  ·
                    rfl

theorem cell23_8118262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_8118262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118262 prefixEnd_8118262 := by exact prefixLift 8118262
  have htrace : WordTrace (prefixWord ++ tailWord_8118262) baseStart_8118262 baseEnd_8118262 := by
    simpa [prefixWord, tailWord_8118262, baseEnd_8118262] using wordTrace_append hprefix tailTrace_8118262
  have hstable : (prefixWord ++ tailWord_8118262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118262).length < 2 ^ (prefixWord ++ tailWord_8118262).sum := by decide
  have hdescent : baseEnd_8118262 < baseStart_8118262 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118282 : List Nat := [3, 1, 2, 2, 4, 1, 2, 1, 2, 3, 2]
def baseStart_8118282 : Nat := 118140960795 + 8118282 * 2 ^ 59
def prefixEnd_8118282 : Nat := 4983230072969 + 3 ^ 40 * 8118282 * 2
def baseEnd_8118282 : Nat := 4168580754743911418039707

theorem tailTrace_8118282 : CollatzResearch.WordTrace tailWord_8118282 prefixEnd_8118282 4168580754743911418039707 := by
  unfold tailWord_8118282
  simp only [CollatzResearch.WordTrace]
  refine ⟨74024517493714570256607275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197398713316572187350952733 74024517493714570256607275)
  ·
    refine ⟨111036776240571855384910913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74024517493714570256607275 111036776240571855384910913)
    ·
      refine ⟨83277582180428891538683185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111036776240571855384910913 83277582180428891538683185)
      ·
        refine ⟨62458186635321668654012389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83277582180428891538683185 62458186635321668654012389)
        ·
          refine ⟨11710909994122812872627323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62458186635321668654012389 11710909994122812872627323)
          ·
            refine ⟨17566364991184219308940985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11710909994122812872627323 17566364991184219308940985)
            ·
              refine ⟨13174773743388164481705739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17566364991184219308940985 13174773743388164481705739)
              ·
                refine ⟨19762160615082246722558609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13174773743388164481705739 19762160615082246722558609)
                ·
                  refine ⟨14821620461311685041918957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19762160615082246722558609 14821620461311685041918957)
                  ·
                    refine ⟨5558107672991881890719609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14821620461311685041918957 5558107672991881890719609)
                    ·
                      refine ⟨4168580754743911418039707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5558107672991881890719609 4168580754743911418039707)
                      ·
                        rfl

theorem cell23_8118282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_8118282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118282 prefixEnd_8118282 := by exact prefixLift 8118282
  have htrace : WordTrace (prefixWord ++ tailWord_8118282) baseStart_8118282 baseEnd_8118282 := by
    simpa [prefixWord, tailWord_8118282, baseEnd_8118282] using wordTrace_append hprefix tailTrace_8118282
  have hstable : (prefixWord ++ tailWord_8118282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118282).length < 2 ^ (prefixWord ++ tailWord_8118282).sum := by decide
  have hdescent : baseEnd_8118282 < baseStart_8118282 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118291 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 4]
def baseStart_8118291 : Nat := 118140960795 + 8118291 * 2 ^ 59
def prefixEnd_8118291 : Nat := 4983230072969 + 3 ^ 40 * 8118291 * 2
def baseEnd_8118291 : Nat := 4168585376069801882827165

theorem tailTrace_8118291 : CollatzResearch.WordTrace tailWord_8118291 prefixEnd_8118291 4168585376069801882827165 := by
  unfold tailWord_8118291
  simp only [CollatzResearch.WordTrace]
  refine ⟨296098398231825675563506727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197398932154550450375671151 296098398231825675563506727)
  ·
    refine ⟨444147597347738513345260091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296098398231825675563506727 444147597347738513345260091)
    ·
      refine ⟨666221396021607770017890137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444147597347738513345260091 666221396021607770017890137)
      ·
        refine ⟨499666047016205827513417603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666221396021607770017890137 499666047016205827513417603)
        ·
          refine ⟨749499070524308741270126405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499666047016205827513417603 749499070524308741270126405)
          ·
            refine ⟨140531075723307888988148701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 749499070524308741270126405 140531075723307888988148701)
            ·
              refine ⟨52699153396240458370555763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140531075723307888988148701 52699153396240458370555763)
              ·
                refine ⟨79048730094360687555833645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52699153396240458370555763 79048730094360687555833645)
                ·
                  refine ⟨29643273785385257833437617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79048730094360687555833645 29643273785385257833437617)
                  ·
                    refine ⟨22232455339038943375078213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29643273785385257833437617 22232455339038943375078213)
                    ·
                      refine ⟨4168585376069801882827165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22232455339038943375078213 4168585376069801882827165)
                      ·
                        rfl

theorem cell23_8118291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_8118291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118291 prefixEnd_8118291 := by exact prefixLift 8118291
  have htrace : WordTrace (prefixWord ++ tailWord_8118291) baseStart_8118291 baseEnd_8118291 := by
    simpa [prefixWord, tailWord_8118291, baseEnd_8118291] using wordTrace_append hprefix tailTrace_8118291
  have hstable : (prefixWord ++ tailWord_8118291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118291).length < 2 ^ (prefixWord ++ tailWord_8118291).sum := by decide
  have hdescent : baseEnd_8118291 < baseStart_8118291 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118298 : List Nat := [3, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5]
def baseStart_8118298 : Nat := 118140960795 + 8118298 * 2 ^ 59
def prefixEnd_8118298 : Nat := 4983230072969 + 3 ^ 40 * 8118298 * 2
def baseEnd_8118298 : Nat := 4168588970434383355439633

theorem tailTrace_8118298 : CollatzResearch.WordTrace tailWord_8118298 prefixEnd_8118298 4168588970434383355439633 := by
  unfold tailWord_8118298
  simp only [CollatzResearch.WordTrace]
  refine ⟨74024663385700078939752887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197399102361866877172674365 74024663385700078939752887)
  ·
    refine ⟨111036995078550118409629331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74024663385700078939752887 111036995078550118409629331)
    ·
      refine ⟨166555492617825177614443997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111036995078550118409629331 166555492617825177614443997)
      ·
        refine ⟨62458309731684441605416499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166555492617825177614443997 62458309731684441605416499)
        ·
          refine ⟨93687464597526662408124749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62458309731684441605416499 93687464597526662408124749)
          ·
            refine ⟨35132799224072498403046781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93687464597526662408124749 35132799224072498403046781)
            ·
              refine ⟨13174799709027186901142543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35132799224072498403046781 13174799709027186901142543)
              ·
                refine ⟨19762199563540780351713815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13174799709027186901142543 19762199563540780351713815)
                ·
                  refine ⟨29643299345311170527570723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19762199563540780351713815 29643299345311170527570723)
                  ·
                    refine ⟨44464949017966755791356085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29643299345311170527570723 44464949017966755791356085)
                    ·
                      refine ⟨4168588970434383355439633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44464949017966755791356085 4168588970434383355439633)
                      ·
                        rfl

theorem cell23_8118298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_8118298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118298 prefixEnd_8118298 := by exact prefixLift 8118298
  have htrace : WordTrace (prefixWord ++ tailWord_8118298) baseStart_8118298 baseEnd_8118298 := by
    simpa [prefixWord, tailWord_8118298, baseEnd_8118298] using wordTrace_append hprefix tailTrace_8118298
  have hstable : (prefixWord ++ tailWord_8118298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118298).length < 2 ^ (prefixWord ++ tailWord_8118298).sum := by decide
  have hdescent : baseEnd_8118298 < baseStart_8118298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118301 : List Nat := [1, 4, 2, 2, 2, 12]
def baseStart_8118301 : Nat := 118140960795 + 8118301 * 2 ^ 59
def prefixEnd_8118301 : Nat := 4983230072969 + 3 ^ 40 * 8118301 * 2
def baseEnd_8118301 : Nat := 17154693460396489068733

theorem tailTrace_8118301 : CollatzResearch.WordTrace tailWord_8118301 prefixEnd_8118301 17154693460396489068733 := by
  unfold tailWord_8118301
  simp only [CollatzResearch.WordTrace]
  refine ⟨296098762961789447271370757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197399175307859631514247171 296098762961789447271370757)
  ·
    refine ⟨55518518055335521363382017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296098762961789447271370757 55518518055335521363382017)
    ·
      refine ⟨41638888541501641022536513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55518518055335521363382017 41638888541501641022536513)
      ·
        refine ⟨31229166406126230766902385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41638888541501641022536513 31229166406126230766902385)
        ·
          refine ⟨23421874804594673075176789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31229166406126230766902385 23421874804594673075176789)
          ·
            refine ⟨17154693460396489068733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 23421874804594673075176789 17154693460396489068733)
            ·
              rfl

theorem cell23_8118301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 12].length) (baseStart_8118301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118301 prefixEnd_8118301 := by exact prefixLift 8118301
  have htrace : WordTrace (prefixWord ++ tailWord_8118301) baseStart_8118301 baseEnd_8118301 := by
    simpa [prefixWord, tailWord_8118301, baseEnd_8118301] using wordTrace_append hprefix tailTrace_8118301
  have hstable : (prefixWord ++ tailWord_8118301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118301).length < 2 ^ (prefixWord ++ tailWord_8118301).sum := by decide
  have hdescent : baseEnd_8118301 < baseStart_8118301 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118318 : List Nat := [4, 1, 3, 1, 1, 2, 3, 8]
def baseStart_8118318 : Nat := 118140960795 + 8118318 * 2 ^ 59
def prefixEnd_8118318 : Nat := 4983230072969 + 3 ^ 40 * 8118318 * 2
def baseEnd_8118318 : Nat := 154392564446202713969983

theorem tailTrace_8118318 : CollatzResearch.WordTrace tailWord_8118318 prefixEnd_8118318 154392564446202713969983 := by
  unfold tailWord_8118318
  simp only [CollatzResearch.WordTrace]
  refine ⟨37012422875340982396842451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197399588668485239449826405 37012422875340982396842451)
  ·
    refine ⟨55518634313011473595263677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37012422875340982396842451 55518634313011473595263677)
    ·
      refine ⟨20819487867379302598223879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55518634313011473595263677 20819487867379302598223879)
      ·
        refine ⟨31229231801068953897335819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20819487867379302598223879 31229231801068953897335819)
        ·
          refine ⟨46843847701603430846003729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31229231801068953897335819 46843847701603430846003729)
          ·
            refine ⟨35132885776202573134502797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46843847701603430846003729 35132885776202573134502797)
            ·
              refine ⟨13174832166075964925438549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35132885776202573134502797 13174832166075964925438549)
              ·
                refine ⟨154392564446202713969983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13174832166075964925438549 154392564446202713969983)
                ·
                  rfl

theorem cell23_8118318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 8].length) (baseStart_8118318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118318 prefixEnd_8118318 := by exact prefixLift 8118318
  have htrace : WordTrace (prefixWord ++ tailWord_8118318) baseStart_8118318 baseEnd_8118318 := by
    simpa [prefixWord, tailWord_8118318, baseEnd_8118318] using wordTrace_append hprefix tailTrace_8118318
  have hstable : (prefixWord ++ tailWord_8118318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118318).length < 2 ^ (prefixWord ++ tailWord_8118318).sum := by decide
  have hdescent : baseEnd_8118318 < baseStart_8118318 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118341 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 2, 2, 5]
def baseStart_8118341 : Nat := 118140960795 + 8118341 * 2 ^ 59
def prefixEnd_8118341 : Nat := 4983230072969 + 3 ^ 40 * 8118341 * 2
def baseEnd_8118341 : Nat := 4168611050102526687201935

theorem tailTrace_8118341 : CollatzResearch.WordTrace tailWord_8118341 prefixEnd_8118341 4168611050102526687201935 := by
  unfold tailWord_8118341
  simp only [CollatzResearch.WordTrace]
  refine ⟨296100221881644534102826877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197400147921096356068551251 296100221881644534102826877)
  ·
    refine ⟨111037583205616700288560079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296100221881644534102826877 111037583205616700288560079)
    ·
      refine ⟨166556374808425050432840119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111037583205616700288560079 166556374808425050432840119)
      ·
        refine ⟨249834562212637575649260179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166556374808425050432840119 249834562212637575649260179)
        ·
          refine ⟨374751843318956363473890269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249834562212637575649260179 374751843318956363473890269)
          ·
            refine ⟨140531941244608636302708851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374751843318956363473890269 140531941244608636302708851)
            ·
              refine ⟨210797911866912954454063277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140531941244608636302708851 210797911866912954454063277)
              ·
                refine ⟨79049216950092357920273729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210797911866912954454063277 79049216950092357920273729)
                ·
                  refine ⟨59286912712569268440205297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79049216950092357920273729 59286912712569268440205297)
                  ·
                    refine ⟨44465184534426951330153973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59286912712569268440205297 44465184534426951330153973)
                    ·
                      refine ⟨4168611050102526687201935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44465184534426951330153973 4168611050102526687201935)
                      ·
                        rfl

theorem cell23_8118341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_8118341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118341 prefixEnd_8118341 := by exact prefixLift 8118341
  have htrace : WordTrace (prefixWord ++ tailWord_8118341) baseStart_8118341 baseEnd_8118341 := by
    simpa [prefixWord, tailWord_8118341, baseEnd_8118341] using wordTrace_append hprefix tailTrace_8118341
  have hstable : (prefixWord ++ tailWord_8118341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118341).length < 2 ^ (prefixWord ++ tailWord_8118341).sum := by decide
  have hdescent : baseEnd_8118341 < baseStart_8118341 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118351 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 4]
def baseStart_8118351 : Nat := 118140960795 + 8118351 * 2 ^ 59
def prefixEnd_8118351 : Nat := 4983230072969 + 3 ^ 40 * 8118351 * 2
def baseEnd_8118351 : Nat := 4168616184909071648076889

theorem tailTrace_8118351 : CollatzResearch.WordTrace tailWord_8118351 prefixEnd_8118351 4168616184909071648076889 := by
  unfold tailWord_8118351
  simp only [CollatzResearch.WordTrace]
  refine ⟨296100586611608305810690907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197400391074405537207127271 296100586611608305810690907)
  ·
    refine ⟨444150879917412458716036361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296100586611608305810690907 444150879917412458716036361)
    ·
      refine ⟨333113159938059344037027271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444150879917412458716036361 333113159938059344037027271)
      ·
        refine ⟨499669739907089016055540907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333113159938059344037027271 499669739907089016055540907)
        ·
          refine ⟨749504609860633524083311361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499669739907089016055540907 749504609860633524083311361)
          ·
            refine ⟨562128457395475143062483521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 749504609860633524083311361 562128457395475143062483521)
            ·
              refine ⟨421596343046606357296862641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562128457395475143062483521 421596343046606357296862641)
              ·
                refine ⟨316197257284954767972646981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421596343046606357296862641 316197257284954767972646981)
                ·
                  refine ⟨59286985740929018994871309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316197257284954767972646981 59286985740929018994871309)
                  ·
                    refine ⟨22232619652848382123076741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59286985740929018994871309 22232619652848382123076741)
                    ·
                      refine ⟨4168616184909071648076889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22232619652848382123076741 4168616184909071648076889)
                      ·
                        rfl

theorem cell23_8118351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_8118351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118351 prefixEnd_8118351 := by exact prefixLift 8118351
  have htrace : WordTrace (prefixWord ++ tailWord_8118351) baseStart_8118351 baseEnd_8118351 := by
    simpa [prefixWord, tailWord_8118351, baseEnd_8118351] using wordTrace_append hprefix tailTrace_8118351
  have hstable : (prefixWord ++ tailWord_8118351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118351).length < 2 ^ (prefixWord ++ tailWord_8118351).sum := by decide
  have hdescent : baseEnd_8118351 < baseStart_8118351 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118361 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 4, 6]
def baseStart_8118361 : Nat := 118140960795 + 8118361 * 2 ^ 59
def prefixEnd_8118361 : Nat := 4983230072969 + 3 ^ 40 * 8118361 * 2
def baseEnd_8118361 : Nat := 1389540439905205536317281

theorem tailTrace_8118361 : CollatzResearch.WordTrace tailWord_8118361 prefixEnd_8118361 1389540439905205536317281 := by
  unfold tailWord_8118361
  simp only [CollatzResearch.WordTrace]
  refine ⟨296100951341572077518554937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197400634227714718345703291 296100951341572077518554937)
  ·
    refine ⟨222075713506179058138916203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296100951341572077518554937 222075713506179058138916203)
    ·
      refine ⟨333113570259268587208374305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222075713506179058138916203 333113570259268587208374305)
      ·
        refine ⟨249835177694451440406280729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333113570259268587208374305 249835177694451440406280729)
        ·
          refine ⟨187376383270838580304710547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249835177694451440406280729 187376383270838580304710547)
          ·
            refine ⟨281064574906257870457065821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187376383270838580304710547 281064574906257870457065821)
            ·
              refine ⟨105399215589846701421399683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281064574906257870457065821 105399215589846701421399683)
              ·
                refine ⟨158098823384770052132099525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105399215589846701421399683 158098823384770052132099525)
                ·
                  refine ⟨29643529384644384774768661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158098823384770052132099525 29643529384644384774768661)
                  ·
                    refine ⟨1389540439905205536317281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29643529384644384774768661 1389540439905205536317281)
                    ·
                      rfl

theorem cell23_8118361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 6].length) (baseStart_8118361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118361 prefixEnd_8118361 := by exact prefixLift 8118361
  have htrace : WordTrace (prefixWord ++ tailWord_8118361) baseStart_8118361 baseEnd_8118361 := by
    simpa [prefixWord, tailWord_8118361, baseEnd_8118361] using wordTrace_append hprefix tailTrace_8118361
  have hstable : (prefixWord ++ tailWord_8118361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118361).length < 2 ^ (prefixWord ++ tailWord_8118361).sum := by decide
  have hdescent : baseEnd_8118361 < baseStart_8118361 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118411 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 6]
def baseStart_8118411 : Nat := 118140960795 + 8118411 * 2 ^ 59
def prefixEnd_8118411 : Nat := 4983230072969 + 3 ^ 40 * 8118411 * 2
def baseEnd_8118411 : Nat := 4168646993748341413326613

theorem tailTrace_8118411 : CollatzResearch.WordTrace tailWord_8118411 prefixEnd_8118411 4168646993748341413326613 := by
  unfold tailWord_8118411
  simp only [CollatzResearch.WordTrace]
  refine ⟨296102774991390936057875087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197401849994260624038583391 296102774991390936057875087)
  ·
    refine ⟨444154162487086404086812631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296102774991390936057875087 444154162487086404086812631)
    ·
      refine ⟨666231243730629606130218947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444154162487086404086812631 666231243730629606130218947)
      ·
        refine ⟨999346865595944409195328421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666231243730629606130218947 999346865595944409195328421)
        ·
          refine ⟨187377537299239576724124079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 999346865595944409195328421 187377537299239576724124079)
          ·
            refine ⟨281066305948859365086186119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187377537299239576724124079 281066305948859365086186119)
            ·
              refine ⟨421599458923289047629279179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281066305948859365086186119 421599458923289047629279179)
              ·
                refine ⟨632399188384933571443918769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421599458923289047629279179 632399188384933571443918769)
                ·
                  refine ⟨474299391288700178582939077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632399188384933571443918769 474299391288700178582939077)
                  ·
                    refine ⟨88931135866631283484301077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 474299391288700178582939077 88931135866631283484301077)
                    ·
                      refine ⟨4168646993748341413326613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88931135866631283484301077 4168646993748341413326613)
                      ·
                        rfl

theorem cell23_8118411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 6].length) (baseStart_8118411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118411 prefixEnd_8118411 := by exact prefixLift 8118411
  have htrace : WordTrace (prefixWord ++ tailWord_8118411) baseStart_8118411 baseEnd_8118411 := by
    simpa [prefixWord, tailWord_8118411, baseEnd_8118411] using wordTrace_append hprefix tailTrace_8118411
  have hstable : (prefixWord ++ tailWord_8118411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118411).length < 2 ^ (prefixWord ++ tailWord_8118411).sum := by decide
  have hdescent : baseEnd_8118411 < baseStart_8118411 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118418 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_8118418 : Nat := 118140960795 + 8118418 * 2 ^ 59
def prefixEnd_8118418 : Nat := 4983230072969 + 3 ^ 40 * 8118418 * 2
def baseEnd_8118418 : Nat := 4168650588112922885939081

theorem tailTrace_8118418 : CollatzResearch.WordTrace tailWord_8118418 prefixEnd_8118418 4168650588112922885939081 := by
  unfold tailWord_8118418
  simp only [CollatzResearch.WordTrace]
  refine ⟨74025757575591394063344977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197402020201577050835586605 74025757575591394063344977)
  ·
    refine ⟨55519318181693545547508733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74025757575591394063344977 55519318181693545547508733)
    ·
      refine ⟨20819744318135079580315775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55519318181693545547508733 20819744318135079580315775)
      ·
        refine ⟨31229616477202619370473663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20819744318135079580315775 31229616477202619370473663)
        ·
          refine ⟨46844424715803929055710495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31229616477202619370473663 46844424715803929055710495)
          ·
            refine ⟨70266637073705893583565743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46844424715803929055710495 70266637073705893583565743)
            ·
              refine ⟨105399955610558840375348615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70266637073705893583565743 105399955610558840375348615)
              ·
                refine ⟨158099933415838260563022923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105399955610558840375348615 158099933415838260563022923)
                ·
                  refine ⟨237149900123757390844534385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158099933415838260563022923 237149900123757390844534385)
                  ·
                    refine ⟨177862425092818043133400789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 237149900123757390844534385 177862425092818043133400789)
                    ·
                      refine ⟨4168650588112922885939081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177862425092818043133400789 4168650588112922885939081)
                      ·
                        rfl

theorem cell23_8118418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_8118418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118418 prefixEnd_8118418 := by exact prefixLift 8118418
  have htrace : WordTrace (prefixWord ++ tailWord_8118418) baseStart_8118418 baseEnd_8118418 := by
    simpa [prefixWord, tailWord_8118418, baseEnd_8118418] using wordTrace_append hprefix tailTrace_8118418
  have hstable : (prefixWord ++ tailWord_8118418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118418).length < 2 ^ (prefixWord ++ tailWord_8118418).sum := by decide
  have hdescent : baseEnd_8118418 < baseStart_8118418 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118455 : List Nat := [1, 1, 3, 1, 4, 3, 2, 1, 2, 5]
def baseStart_8118455 : Nat := 118140960795 + 8118455 * 2 ^ 59
def prefixEnd_8118455 : Nat := 4983230072969 + 3 ^ 40 * 8118455 * 2
def baseEnd_8118455 : Nat := 1389556528965713080392137

theorem tailTrace_8118455 : CollatzResearch.WordTrace tailWord_8118455 prefixEnd_8118455 1389556528965713080392137 := by
  unfold tailWord_8118455
  simp only [CollatzResearch.WordTrace]
  refine ⟨296104379803231531572476819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197402919868821021048317879 296104379803231531572476819)
  ·
    refine ⟨444156569704847297358715229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296104379803231531572476819 444156569704847297358715229)
    ·
      refine ⟨166558713639317736509518211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444156569704847297358715229 166558713639317736509518211)
      ·
        refine ⟨249838070458976604764277317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166558713639317736509518211 249838070458976604764277317)
        ·
          refine ⟨46844638211058113393301997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249838070458976604764277317 46844638211058113393301997)
          ·
            refine ⟨17566739329146792522488249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46844638211058113393301997 17566739329146792522488249)
            ·
              refine ⟨13175054496860094391866187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17566739329146792522488249 13175054496860094391866187)
              ·
                refine ⟨19762581745290141587799281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13175054496860094391866187 19762581745290141587799281)
                ·
                  refine ⟨14821936308967606190849461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19762581745290141587799281 14821936308967606190849461)
                  ·
                    refine ⟨1389556528965713080392137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14821936308967606190849461 1389556528965713080392137)
                    ·
                      rfl

theorem cell23_8118455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_8118455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118455 prefixEnd_8118455 := by exact prefixLift 8118455
  have htrace : WordTrace (prefixWord ++ tailWord_8118455) baseStart_8118455 baseEnd_8118455 := by
    simpa [prefixWord, tailWord_8118455, baseEnd_8118455] using wordTrace_append hprefix tailTrace_8118455
  have hstable : (prefixWord ++ tailWord_8118455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118455).length < 2 ^ (prefixWord ++ tailWord_8118455).sum := by decide
  have hdescent : baseEnd_8118455 < baseStart_8118455 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118458 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4]
def baseStart_8118458 : Nat := 118140960795 + 8118458 * 2 ^ 59
def prefixEnd_8118458 : Nat := 4983230072969 + 3 ^ 40 * 8118458 * 2
def baseEnd_8118458 : Nat := 4168671127339102729438897

theorem tailTrace_8118458 : CollatzResearch.WordTrace tailWord_8118458 prefixEnd_8118458 4168671127339102729438897 := by
  unfold tailWord_8118458
  simp only [CollatzResearch.WordTrace]
  refine ⟨74026122305555165771209007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197402992814813775389890685 74026122305555165771209007)
  ·
    refine ⟨111039183458332748656813511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74026122305555165771209007 111039183458332748656813511)
    ·
      refine ⟨166558775187499122985220267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111039183458332748656813511 166558775187499122985220267)
      ·
        refine ⟨249838162781248684477830401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166558775187499122985220267 249838162781248684477830401)
        ·
          refine ⟨187378622085936513358372801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249838162781248684477830401 187378622085936513358372801)
          ·
            refine ⟨140533966564452385018779601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187378622085936513358372801 140533966564452385018779601)
            ·
              refine ⟨105400474923339288764084701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140533966564452385018779601 105400474923339288764084701)
              ·
                refine ⟨39525178096252233286531763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105400474923339288764084701 39525178096252233286531763)
                ·
                  refine ⟨59287767144378349929797645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39525178096252233286531763 59287767144378349929797645)
                  ·
                    refine ⟨22232912679141881223674117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59287767144378349929797645 22232912679141881223674117)
                    ·
                      refine ⟨4168671127339102729438897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22232912679141881223674117 4168671127339102729438897)
                      ·
                        rfl

theorem cell23_8118458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_8118458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118458 prefixEnd_8118458 := by exact prefixLift 8118458
  have htrace : WordTrace (prefixWord ++ tailWord_8118458) baseStart_8118458 baseEnd_8118458 := by
    simpa [prefixWord, tailWord_8118458, baseEnd_8118458] using wordTrace_append hprefix tailTrace_8118458
  have hstable : (prefixWord ++ tailWord_8118458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118458).length < 2 ^ (prefixWord ++ tailWord_8118458).sum := by decide
  have hdescent : baseEnd_8118458 < baseStart_8118458 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118475 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 2, 4, 2]
def baseStart_8118475 : Nat := 118140960795 + 8118475 * 2 ^ 59
def prefixEnd_8118475 : Nat := 4983230072969 + 3 ^ 40 * 8118475 * 2
def baseEnd_8118475 : Nat := 4168679856510229162926319

theorem tailTrace_8118475 : CollatzResearch.WordTrace tailWord_8118475 prefixEnd_8118475 4168679856510229162926319 := by
  unfold tailWord_8118475
  simp only [CollatzResearch.WordTrace]
  refine ⟨296105109263159074988204879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197403406175439383325469919 296105109263159074988204879)
  ·
    refine ⟨444157663894738612482307319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296105109263159074988204879 444157663894738612482307319)
    ·
      refine ⟨666236495842107918723460979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444157663894738612482307319 666236495842107918723460979)
      ·
        refine ⟨999354743763161878085191469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666236495842107918723460979 999354743763161878085191469)
        ·
          refine ⟨374758028911185704281946801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 999354743763161878085191469 374758028911185704281946801)
          ·
            refine ⟨281068521683389278211460101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374758028911185704281946801 281068521683389278211460101)
            ·
              refine ⟨52700347815635489664648769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281068521683389278211460101 52700347815635489664648769)
              ·
                refine ⟨39525260861726617248486577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52700347815635489664648769 39525260861726617248486577)
                ·
                  refine ⟨29643945646294962936364933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39525260861726617248486577 29643945646294962936364933)
                  ·
                    refine ⟨5558239808680305550568425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29643945646294962936364933 5558239808680305550568425)
                    ·
                      refine ⟨4168679856510229162926319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5558239808680305550568425 4168679856510229162926319)
                      ·
                        rfl

theorem cell23_8118475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 4, 2].length) (baseStart_8118475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118475 prefixEnd_8118475 := by exact prefixLift 8118475
  have htrace : WordTrace (prefixWord ++ tailWord_8118475) baseStart_8118475 baseEnd_8118475 := by
    simpa [prefixWord, tailWord_8118475, baseEnd_8118475] using wordTrace_append hprefix tailTrace_8118475
  have hstable : (prefixWord ++ tailWord_8118475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118475).length < 2 ^ (prefixWord ++ tailWord_8118475).sum := by decide
  have hdescent : baseEnd_8118475 < baseStart_8118475 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118476 : List Nat := [2, 2, 1, 6, 1, 2, 2, 2, 5]
def baseStart_8118476 : Nat := 118140960795 + 8118476 * 2 ^ 59
def prefixEnd_8118476 : Nat := 4983230072969 + 3 ^ 40 * 8118476 * 2
def baseEnd_8118476 : Nat := 463186707776764851001535

theorem tailTrace_8118476 : CollatzResearch.WordTrace tailWord_8118476 prefixEnd_8118476 463186707776764851001535 := by
  unfold tailWord_8118476
  simp only [CollatzResearch.WordTrace]
  refine ⟨148052572868077726079495641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197403430490770301439327521 148052572868077726079495641)
  ·
    refine ⟨111039429651058294559621731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148052572868077726079495641 111039429651058294559621731)
    ·
      refine ⟨166559144476587441839432597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111039429651058294559621731 166559144476587441839432597)
      ·
        refine ⟨7807459897340036336223403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 166559144476587441839432597 7807459897340036336223403)
        ·
          refine ⟨11711189846010054504335105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7807459897340036336223403 11711189846010054504335105)
          ·
            refine ⟨8783392384507540878251329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11711189846010054504335105 8783392384507540878251329)
            ·
              refine ⟨6587544288380655658688497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8783392384507540878251329 6587544288380655658688497)
              ·
                refine ⟨4940658216285491744016373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6587544288380655658688497 4940658216285491744016373)
                ·
                  refine ⟨463186707776764851001535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4940658216285491744016373 463186707776764851001535)
                  ·
                    rfl

theorem cell23_8118476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 5].length) (baseStart_8118476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118476 prefixEnd_8118476 := by exact prefixLift 8118476
  have htrace : WordTrace (prefixWord ++ tailWord_8118476) baseStart_8118476 baseEnd_8118476 := by
    simpa [prefixWord, tailWord_8118476, baseEnd_8118476] using wordTrace_append hprefix tailTrace_8118476
  have hstable : (prefixWord ++ tailWord_8118476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118476).length < 2 ^ (prefixWord ++ tailWord_8118476).sum := by decide
  have hdescent : baseEnd_8118476 < baseStart_8118476 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118509 : List Nat := [1, 5, 1, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_8118509 : Nat := 118140960795 + 8118509 * 2 ^ 59
def prefixEnd_8118509 : Nat := 4983230072969 + 3 ^ 40 * 8118509 * 2
def baseEnd_8118509 : Nat := 4168697314852482029901163

theorem tailTrace_8118509 : CollatzResearch.WordTrace tailWord_8118509 prefixEnd_8118509 4168697314852482029901163 := by
  unfold tailWord_8118509
  simp only [CollatzResearch.WordTrace]
  refine ⟨296106349345035898794942581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197404232896690599196628387 296106349345035898794942581)
  ·
    refine ⟨27759970251097115512025867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 296106349345035898794942581 27759970251097115512025867)
    ·
      refine ⟨41639955376645673268038801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27759970251097115512025867 41639955376645673268038801)
      ·
        refine ⟨31229966532484254951029101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41639955376645673268038801 31229966532484254951029101)
        ·
          refine ⟨11711237449681595606635913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31229966532484254951029101 11711237449681595606635913)
          ·
            refine ⟨8783428087261196704976935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11711237449681595606635913 8783428087261196704976935)
            ·
              refine ⟨13175142130891795057465403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8783428087261196704976935 13175142130891795057465403)
              ·
                refine ⟨19762713196337692586198105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13175142130891795057465403 19762713196337692586198105)
                ·
                  refine ⟨14822034897253269439648579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19762713196337692586198105 14822034897253269439648579)
                  ·
                    refine ⟨22233052345879904159472869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14822034897253269439648579 22233052345879904159472869)
                    ·
                      refine ⟨4168697314852482029901163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22233052345879904159472869 4168697314852482029901163)
                      ·
                        rfl

theorem cell23_8118509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_8118509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118509 prefixEnd_8118509 := by exact prefixLift 8118509
  have htrace : WordTrace (prefixWord ++ tailWord_8118509) baseStart_8118509 baseEnd_8118509 := by
    simpa [prefixWord, tailWord_8118509, baseEnd_8118509] using wordTrace_append hprefix tailTrace_8118509
  have hstable : (prefixWord ++ tailWord_8118509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118509).length < 2 ^ (prefixWord ++ tailWord_8118509).sum := by decide
  have hdescent : baseEnd_8118509 < baseStart_8118509 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118562 : List Nat := [3, 3, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_8118562 : Nat := 118140960795 + 8118562 * 2 ^ 59
def prefixEnd_8118562 : Nat := 4983230072969 + 3 ^ 40 * 8118562 * 2
def baseEnd_8118562 : Nat := 1389574843109056774179473

theorem tailTrace_8118562 : CollatzResearch.WordTrace tailWord_8118562 prefixEnd_8118562 1389574843109056774179473 := by
  unfold tailWord_8118562
  simp only [CollatzResearch.WordTrace]
  refine ⟨74027070603460972211655485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197405521609229259231081293 74027070603460972211655485)
  ·
    refine ⟨27760151476297864579370807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74027070603460972211655485 27760151476297864579370807)
    ·
      refine ⟨41640227214446796869056211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27760151476297864579370807 41640227214446796869056211)
      ·
        refine ⟨62460340821670195303584317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41640227214446796869056211 62460340821670195303584317)
        ·
          refine ⟨23422627808126323238844119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62460340821670195303584317 23422627808126323238844119)
          ·
            refine ⟨35133941712189484858266179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23422627808126323238844119 35133941712189484858266179)
            ·
              refine ⟨52700912568284227287399269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35133941712189484858266179 52700912568284227287399269)
              ·
                refine ⟨9881421106553292616387363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52700912568284227287399269 9881421106553292616387363)
                ·
                  refine ⟨14822131659829938924581045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9881421106553292616387363 14822131659829938924581045)
                  ·
                    refine ⟨1389574843109056774179473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14822131659829938924581045 1389574843109056774179473)
                    ·
                      rfl

theorem cell23_8118562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_8118562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118562 prefixEnd_8118562 := by exact prefixLift 8118562
  have htrace : WordTrace (prefixWord ++ tailWord_8118562) baseStart_8118562 baseEnd_8118562 := by
    simpa [prefixWord, tailWord_8118562, baseEnd_8118562] using wordTrace_append hprefix tailTrace_8118562
  have hstable : (prefixWord ++ tailWord_8118562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118562).length < 2 ^ (prefixWord ++ tailWord_8118562).sum := by decide
  have hdescent : baseEnd_8118562 < baseStart_8118562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118575 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 4, 4]
def baseStart_8118575 : Nat := 118140960795 + 8118575 * 2 ^ 59
def prefixEnd_8118575 : Nat := 4983230072969 + 3 ^ 40 * 8118575 * 2
def baseEnd_8118575 : Nat := 1389577068191892923891953

theorem tailTrace_8118575 : CollatzResearch.WordTrace tailWord_8118575 prefixEnd_8118575 1389577068191892923891953 := by
  unfold tailWord_8118575
  simp only [CollatzResearch.WordTrace]
  refine ⟨296108756562796792066845179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197405837708531194711230119 296108756562796792066845179)
  ·
    refine ⟨444163134844195188100267769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296108756562796792066845179 444163134844195188100267769)
    ·
      refine ⟨333122351133146391075200827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444163134844195188100267769 333122351133146391075200827)
      ·
        refine ⟨499683526699719586612801241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333122351133146391075200827 499683526699719586612801241)
        ·
          refine ⟨374762645024789689959600931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499683526699719586612801241 374762645024789689959600931)
          ·
            refine ⟨562143967537184534939401397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374762645024789689959600931 562143967537184534939401397)
            ·
              refine ⟨52700996956611050150568881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 562143967537184534939401397 52700996956611050150568881)
              ·
                refine ⟨39525747717458287612926661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52700996956611050150568881 39525747717458287612926661)
                ·
                  refine ⟨7411077697023428927423749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39525747717458287612926661 7411077697023428927423749)
                  ·
                    refine ⟨1389577068191892923891953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7411077697023428927423749 1389577068191892923891953)
                    ·
                      rfl

theorem cell23_8118575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 4].length) (baseStart_8118575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118575 prefixEnd_8118575 := by exact prefixLift 8118575
  have htrace : WordTrace (prefixWord ++ tailWord_8118575) baseStart_8118575 baseEnd_8118575 := by
    simpa [prefixWord, tailWord_8118575, baseEnd_8118575] using wordTrace_append hprefix tailTrace_8118575
  have hstable : (prefixWord ++ tailWord_8118575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118575).length < 2 ^ (prefixWord ++ tailWord_8118575).sum := by decide
  have hdescent : baseEnd_8118575 < baseStart_8118575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118593 : List Nat := [1, 2, 5, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_8118593 : Nat := 118140960795 + 8118593 * 2 ^ 59
def prefixEnd_8118593 : Nat := 4983230072969 + 3 ^ 40 * 8118593 * 2
def baseEnd_8118593 : Nat := 4168740447227459701250777

theorem tailTrace_8118593 : CollatzResearch.WordTrace tailWord_8118593 prefixEnd_8118593 4168740447227459701250777 := by
  unfold tailWord_8118593
  simp only [CollatzResearch.WordTrace]
  refine ⟨296109413076731581141000433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197406275384487720760666955 296109413076731581141000433)
  ·
    refine ⟨222082059807548685855750325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296109413076731581141000433 222082059807548685855750325)
    ·
      refine ⟨20820193106957689298976593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222082059807548685855750325 20820193106957689298976593)
      ·
        refine ⟨15615144830218266974232445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20820193106957689298976593 15615144830218266974232445)
        ·
          refine ⟨5855679311331850115337167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15615144830218266974232445 5855679311331850115337167)
          ·
            refine ⟨8783518966997775173005751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5855679311331850115337167 8783518966997775173005751)
            ·
              refine ⟨13175278450496662759508627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8783518966997775173005751 13175278450496662759508627)
              ·
                refine ⟨19762917675744994139262941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13175278450496662759508627 19762917675744994139262941)
                ·
                  refine ⟨7411094128404372802223603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19762917675744994139262941 7411094128404372802223603)
                  ·
                    refine ⟨11116641192606559203335405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7411094128404372802223603 11116641192606559203335405)
                    ·
                      refine ⟨4168740447227459701250777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11116641192606559203335405 4168740447227459701250777)
                      ·
                        rfl

theorem cell23_8118593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_8118593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118593 prefixEnd_8118593 := by exact prefixLift 8118593
  have htrace : WordTrace (prefixWord ++ tailWord_8118593) baseStart_8118593 baseEnd_8118593 := by
    simpa [prefixWord, tailWord_8118593, baseEnd_8118593] using wordTrace_append hprefix tailTrace_8118593
  have hstable : (prefixWord ++ tailWord_8118593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118593).length < 2 ^ (prefixWord ++ tailWord_8118593).sum := by decide
  have hdescent : baseEnd_8118593 < baseStart_8118593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118609 : List Nat := [1, 2, 2, 1, 4, 2, 4, 1, 2, 4]
def baseStart_8118609 : Nat := 118140960795 + 8118609 * 2 ^ 59
def prefixEnd_8118609 : Nat := 4983230072969 + 3 ^ 40 * 8118609 * 2
def baseEnd_8118609 : Nat := 1389582887639310546216901

theorem tailTrace_8118609 : CollatzResearch.WordTrace tailWord_8118609 prefixEnd_8118609 1389582887639310546216901 := by
  unfold tailWord_8118609
  simp only [CollatzResearch.WordTrace]
  refine ⟨296109996644673615873582881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197406664429782410582388587 296109996644673615873582881)
  ·
    refine ⟨222082497483505211905187161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296109996644673615873582881 222082497483505211905187161)
    ·
      refine ⟨166561873112628908928890371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222082497483505211905187161 166561873112628908928890371)
      ·
        refine ⟨249842809668943363393335557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166561873112628908928890371 249842809668943363393335557)
        ·
          refine ⟨46845526812926880636250417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249842809668943363393335557 46845526812926880636250417)
          ·
            refine ⟨35134145109695160477187813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46845526812926880636250417 35134145109695160477187813)
            ·
              refine ⟨6587652208067842589472715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35134145109695160477187813 6587652208067842589472715)
              ·
                refine ⟨9881478312101763884209073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6587652208067842589472715 9881478312101763884209073)
                ·
                  refine ⟨7411108734076322913156805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9881478312101763884209073 7411108734076322913156805)
                  ·
                    refine ⟨1389582887639310546216901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7411108734076322913156805 1389582887639310546216901)
                    ·
                      rfl

theorem cell23_8118609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 2, 4].length) (baseStart_8118609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118609 prefixEnd_8118609 := by exact prefixLift 8118609
  have htrace : WordTrace (prefixWord ++ tailWord_8118609) baseStart_8118609 baseEnd_8118609 := by
    simpa [prefixWord, tailWord_8118609, baseEnd_8118609] using wordTrace_append hprefix tailTrace_8118609
  have hstable : (prefixWord ++ tailWord_8118609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118609).length < 2 ^ (prefixWord ++ tailWord_8118609).sum := by decide
  have hdescent : baseEnd_8118609 < baseStart_8118609 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118632 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_8118632 : Nat := 118140960795 + 8118632 * 2 ^ 59
def prefixEnd_8118632 : Nat := 4983230072969 + 3 ^ 40 * 8118632 * 2
def baseEnd_8118632 : Nat := 4168760472972985048663097

theorem tailTrace_8118632 : CollatzResearch.WordTrace tailWord_8118632 prefixEnd_8118632 4168760472972985048663097 := by
  unfold tailWord_8118632
  simp only [CollatzResearch.WordTrace]
  refine ⟨148055417761795145400835075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197407223682393527201113433 148055417761795145400835075)
  ·
    refine ⟨222083126642692718101252613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148055417761795145400835075 222083126642692718101252613)
    ·
      refine ⟨41640586245504884643984865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222083126642692718101252613 41640586245504884643984865)
      ·
        refine ⟨31230439684128663482988649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41640586245504884643984865 31230439684128663482988649)
        ·
          refine ⟨23422829763096497612241487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31230439684128663482988649 23422829763096497612241487)
          ·
            refine ⟨35134244644644746418362231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23422829763096497612241487 35134244644644746418362231)
            ·
              refine ⟨52701366966967119627543347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35134244644644746418362231 52701366966967119627543347)
              ·
                refine ⟨79052050450450679441315021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52701366966967119627543347 79052050450450679441315021)
                ·
                  refine ⟨29644518918919004790493133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79052050450450679441315021 29644518918919004790493133)
                  ·
                    refine ⟨11116694594594626796434925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29644518918919004790493133 11116694594594626796434925)
                    ·
                      refine ⟨4168760472972985048663097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11116694594594626796434925 4168760472972985048663097)
                      ·
                        rfl

theorem cell23_8118632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_8118632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118632 prefixEnd_8118632 := by exact prefixLift 8118632
  have htrace : WordTrace (prefixWord ++ tailWord_8118632) baseStart_8118632 baseEnd_8118632 := by
    simpa [prefixWord, tailWord_8118632, baseEnd_8118632] using wordTrace_append hprefix tailTrace_8118632
  have hstable : (prefixWord ++ tailWord_8118632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118632).length < 2 ^ (prefixWord ++ tailWord_8118632).sum := by decide
  have hdescent : baseEnd_8118632 < baseStart_8118632 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118636 : List Nat := [2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 3]
def baseStart_8118636 : Nat := 118140960795 + 8118636 * 2 ^ 59
def prefixEnd_8118636 : Nat := 4983230072969 + 3 ^ 40 * 8118636 * 2
def baseEnd_8118636 : Nat := 4168762526895603033013079

theorem tailTrace_8118636 : CollatzResearch.WordTrace tailWord_8118636 prefixEnd_8118636 4168762526895603033013079 := by
  unfold tailWord_8118636
  simp only [CollatzResearch.WordTrace]
  refine ⟨148055490707787899742407881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197407320943717199656543841 148055490707787899742407881)
  ·
    refine ⟨111041618030840924806805911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148055490707787899742407881 111041618030840924806805911)
    ·
      refine ⟨166562427046261387210208867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111041618030840924806805911 166562427046261387210208867)
      ·
        refine ⟨249843640569392080815313301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166562427046261387210208867 249843640569392080815313301)
        ·
          refine ⟨11711420651690253788217811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 249843640569392080815313301 11711420651690253788217811)
          ·
            refine ⟨17567130977535380682326717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11711420651690253788217811 17567130977535380682326717)
            ·
              refine ⟨6587674116575767755872519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17567130977535380682326717 6587674116575767755872519)
              ·
                refine ⟨9881511174863651633808779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6587674116575767755872519 9881511174863651633808779)
                ·
                  refine ⟨14822266762295477450713169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9881511174863651633808779 14822266762295477450713169)
                  ·
                    refine ⟨11116700071721608088034877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14822266762295477450713169 11116700071721608088034877)
                    ·
                      refine ⟨4168762526895603033013079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11116700071721608088034877 4168762526895603033013079)
                      ·
                        rfl

theorem cell23_8118636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 3].length) (baseStart_8118636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118636 prefixEnd_8118636 := by exact prefixLift 8118636
  have htrace : WordTrace (prefixWord ++ tailWord_8118636) baseStart_8118636 baseEnd_8118636 := by
    simpa [prefixWord, tailWord_8118636, baseEnd_8118636] using wordTrace_append hprefix tailTrace_8118636
  have hstable : (prefixWord ++ tailWord_8118636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118636).length < 2 ^ (prefixWord ++ tailWord_8118636).sum := by decide
  have hdescent : baseEnd_8118636 < baseStart_8118636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118665 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 1, 8]
def baseStart_8118665 : Nat := 118140960795 + 8118665 * 2 ^ 59
def prefixEnd_8118665 : Nat := 4983230072969 + 3 ^ 40 * 8118665 * 2
def baseEnd_8118665 : Nat := 1389592472611527806516815

theorem tailTrace_8118665 : CollatzResearch.WordTrace tailWord_8118665 prefixEnd_8118665 1389592472611527806516815 := by
  unfold tailWord_8118665
  simp only [CollatzResearch.WordTrace]
  refine ⟨296112039132470737437621449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197408026088313824958414299 296112039132470737437621449)
  ·
    refine ⟨222084029349353053078216087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296112039132470737437621449 222084029349353053078216087)
    ·
      refine ⟨333126044024029579617324131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222084029349353053078216087 333126044024029579617324131)
      ·
        refine ⟨499689066036044369425986197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333126044024029579617324131 499689066036044369425986197)
        ·
          refine ⟨23422924970439579816843103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 499689066036044369425986197 23422924970439579816843103)
          ·
            refine ⟨35134387455659369725264655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23422924970439579816843103 35134387455659369725264655)
            ·
              refine ⟨52701581183489054587896983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35134387455659369725264655 52701581183489054587896983)
              ·
                refine ⟨79052371775233581881845475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52701581183489054587896983 79052371775233581881845475)
                ·
                  refine ⟨118578557662850372822768213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79052371775233581881845475 118578557662850372822768213)
                  ·
                    refine ⟨1389592472611527806516815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118578557662850372822768213 1389592472611527806516815)
                    ·
                      rfl

theorem cell23_8118665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 8].length) (baseStart_8118665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118665 prefixEnd_8118665 := by exact prefixLift 8118665
  have htrace : WordTrace (prefixWord ++ tailWord_8118665) baseStart_8118665 baseEnd_8118665 := by
    simpa [prefixWord, tailWord_8118665, baseEnd_8118665] using wordTrace_append hprefix tailTrace_8118665
  have hstable : (prefixWord ++ tailWord_8118665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118665).length < 2 ^ (prefixWord ++ tailWord_8118665).sum := by decide
  have hdescent : baseEnd_8118665 < baseStart_8118665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118666 : List Nat := [3, 1, 2, 5, 1, 1, 2, 1, 1, 3, 3]
def baseStart_8118666 : Nat := 118140960795 + 8118666 * 2 ^ 59
def prefixEnd_8118666 : Nat := 4983230072969 + 3 ^ 40 * 8118666 * 2
def baseEnd_8118666 : Nat := 4168777931315237915637941

theorem tailTrace_8118666 : CollatzResearch.WordTrace tailWord_8118666 prefixEnd_8118666 4168777931315237915637941 := by
  unfold tailWord_8118666
  simp only [CollatzResearch.WordTrace]
  refine ⟨74028018901366778652101963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197408050403644743072271901 74028018901366778652101963)
  ·
    refine ⟨111042028352050167978152945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74028018901366778652101963 111042028352050167978152945)
    ·
      refine ⟨83281521264037625983614709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111042028352050167978152945 83281521264037625983614709)
      ·
        refine ⟨7807642618503527435963879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83281521264037625983614709 7807642618503527435963879)
        ·
          refine ⟨11711463927755291153945819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7807642618503527435963879 11711463927755291153945819)
          ·
            refine ⟨17567195891632936730918729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11711463927755291153945819 17567195891632936730918729)
            ·
              refine ⟨13175396918724702548189047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17567195891632936730918729 13175396918724702548189047)
              ·
                refine ⟨19763095378087053822283571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13175396918724702548189047 19763095378087053822283571)
                ·
                  refine ⟨29644643067130580733425357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19763095378087053822283571 29644643067130580733425357)
                  ·
                    refine ⟨11116741150173967775034509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29644643067130580733425357 11116741150173967775034509)
                    ·
                      refine ⟨4168777931315237915637941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11116741150173967775034509 4168777931315237915637941)
                      ·
                        rfl

theorem cell23_8118666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_8118666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118666 prefixEnd_8118666 := by exact prefixLift 8118666
  have htrace : WordTrace (prefixWord ++ tailWord_8118666) baseStart_8118666 baseEnd_8118666 := by
    simpa [prefixWord, tailWord_8118666, baseEnd_8118666] using wordTrace_append hprefix tailTrace_8118666
  have hstable : (prefixWord ++ tailWord_8118666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118666).length < 2 ^ (prefixWord ++ tailWord_8118666).sum := by decide
  have hdescent : baseEnd_8118666 < baseStart_8118666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118735 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 5]
def baseStart_8118735 : Nat := 118140960795 + 8118735 * 2 ^ 59
def prefixEnd_8118735 : Nat := 4983230072969 + 3 ^ 40 * 8118735 * 2
def baseEnd_8118735 : Nat := 4168813361480398145675123

theorem tailTrace_8118735 : CollatzResearch.WordTrace tailWord_8118735 prefixEnd_8118735 4168813361480398145675123 := by
  unfold tailWord_8118735
  simp only [CollatzResearch.WordTrace]
  refine ⟨296114592242217139392669659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197409728161478092928446439 296114592242217139392669659)
  ·
    refine ⟨444171888363325709089004489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296114592242217139392669659 444171888363325709089004489)
    ·
      refine ⟨333128916272494281816753367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444171888363325709089004489 333128916272494281816753367)
      ·
        refine ⟨499693374408741422725130051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333128916272494281816753367 499693374408741422725130051)
        ·
          refine ⟨749540061613112134087695077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499693374408741422725130051 749540061613112134087695077)
          ·
            refine ⟨140538761552458525141442827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 749540061613112134087695077 140538761552458525141442827)
            ·
              refine ⟨210808142328687787712164241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140538761552458525141442827 210808142328687787712164241)
              ·
                refine ⟨158106106746515840784123181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210808142328687787712164241 158106106746515840784123181)
                ·
                  refine ⟨59289790029943440294046193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158106106746515840784123181 59289790029943440294046193)
                  ·
                    refine ⟨44467342522457580220534645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59289790029943440294046193 44467342522457580220534645)
                    ·
                      refine ⟨4168813361480398145675123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44467342522457580220534645 4168813361480398145675123)
                      ·
                        rfl

theorem cell23_8118735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_8118735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118735 prefixEnd_8118735 := by exact prefixLift 8118735
  have htrace : WordTrace (prefixWord ++ tailWord_8118735) baseStart_8118735 baseEnd_8118735 := by
    simpa [prefixWord, tailWord_8118735, baseEnd_8118735] using wordTrace_append hprefix tailTrace_8118735
  have hstable : (prefixWord ++ tailWord_8118735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118735).length < 2 ^ (prefixWord ++ tailWord_8118735).sum := by decide
  have hdescent : baseEnd_8118735 < baseStart_8118735 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118775 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 6]
def baseStart_8118775 : Nat := 118140960795 + 8118775 * 2 ^ 59
def prefixEnd_8118775 : Nat := 4983230072969 + 3 ^ 40 * 8118775 * 2
def baseEnd_8118775 : Nat := 4168833900706577989174939

theorem tailTrace_8118775 : CollatzResearch.WordTrace tailWord_8118775 prefixEnd_8118775 4168833900706577989174939 := by
  unfold tailWord_8118775
  simp only [CollatzResearch.WordTrace]
  refine ⟨296116051162072226224125779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197410700774714817482750519 296116051162072226224125779)
  ·
    refine ⟨444174076743108339336188669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296116051162072226224125779 444174076743108339336188669)
    ·
      refine ⟨166565278778665627251070751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444174076743108339336188669 166565278778665627251070751)
      ·
        refine ⟨249847918167998440876606127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166565278778665627251070751 249847918167998440876606127)
        ·
          refine ⟨374771877251997661314909191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249847918167998440876606127 374771877251997661314909191)
          ·
            refine ⟨562157815877996491972363787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374771877251997661314909191 562157815877996491972363787)
            ·
              refine ⟨843236723816994737958545681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562157815877996491972363787 843236723816994737958545681)
              ·
                refine ⟨632427542862746053468909261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843236723816994737958545681 632427542862746053468909261)
                ·
                  refine ⟨237160328573529770050840973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632427542862746053468909261 237160328573529770050840973)
                  ·
                    refine ⟨88935123215073663769065365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237160328573529770050840973 88935123215073663769065365)
                    ·
                      refine ⟨4168833900706577989174939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88935123215073663769065365 4168833900706577989174939)
                      ·
                        rfl

theorem cell23_8118775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_8118775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118775 prefixEnd_8118775 := by exact prefixLift 8118775
  have htrace : WordTrace (prefixWord ++ tailWord_8118775) baseStart_8118775 baseEnd_8118775 := by
    simpa [prefixWord, tailWord_8118775, baseEnd_8118775] using wordTrace_append hprefix tailTrace_8118775
  have hstable : (prefixWord ++ tailWord_8118775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118775).length < 2 ^ (prefixWord ++ tailWord_8118775).sum := by decide
  have hdescent : baseEnd_8118775 < baseStart_8118775 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118819 : List Nat := [1, 1, 1, 4, 4, 2, 2, 2, 6]
def baseStart_8118819 : Nat := 118140960795 + 8118819 * 2 ^ 59
def prefixEnd_8118819 : Nat := 4983230072969 + 3 ^ 40 * 8118819 * 2
def baseEnd_8118819 : Nat := 463206277095041757447193

theorem tailTrace_8118819 : CollatzResearch.WordTrace tailWord_8118819 prefixEnd_8118819 463206277095041757447193 := by
  unfold tailWord_8118819
  simp only [CollatzResearch.WordTrace]
  refine ⟨296117655973912821738727511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197411770649275214492485007 296117655973912821738727511)
  ·
    refine ⟨444176483960869232608091267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296117655973912821738727511 444176483960869232608091267)
    ·
      refine ⟨666264725941303848912136901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444176483960869232608091267 666264725941303848912136901)
      ·
        refine ⟨124924636113994471671025669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 666264725941303848912136901 124924636113994471671025669)
        ·
          refine ⟨23423369271373963438317313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124924636113994471671025669 23423369271373963438317313)
          ·
            refine ⟨17567526953530472578737985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23423369271373963438317313 17567526953530472578737985)
            ·
              refine ⟨13175645215147854434053489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17567526953530472578737985 13175645215147854434053489)
              ·
                refine ⟨9881733911360890825540117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13175645215147854434053489 9881733911360890825540117)
                ·
                  refine ⟨463206277095041757447193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9881733911360890825540117 463206277095041757447193)
                  ·
                    rfl

theorem cell23_8118819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 6].length) (baseStart_8118819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118819 prefixEnd_8118819 := by exact prefixLift 8118819
  have htrace : WordTrace (prefixWord ++ tailWord_8118819) baseStart_8118819 baseEnd_8118819 := by
    simpa [prefixWord, tailWord_8118819, baseEnd_8118819] using wordTrace_append hprefix tailTrace_8118819
  have hstable : (prefixWord ++ tailWord_8118819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118819).length < 2 ^ (prefixWord ++ tailWord_8118819).sum := by decide
  have hdescent : baseEnd_8118819 < baseStart_8118819 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118832 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 3, 5]
def baseStart_8118832 : Nat := 118140960795 + 8118832 * 2 ^ 59
def prefixEnd_8118832 : Nat := 4983230072969 + 3 ^ 40 * 8118832 * 2
def baseEnd_8118832 : Nat := 1389621056367961422054059

theorem tailTrace_8118832 : CollatzResearch.WordTrace tailWord_8118832 prefixEnd_8118832 1389621056367961422054059 := by
  unfold tailWord_8118832
  simp only [CollatzResearch.WordTrace]
  refine ⟨148059065061432862479475375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197412086748577149972633833 148059065061432862479475375)
  ·
    refine ⟨222088597592149293719213063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148059065061432862479475375 222088597592149293719213063)
    ·
      refine ⟨333132896388223940578819595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222088597592149293719213063 333132896388223940578819595)
      ·
        refine ⟨499699344582335910868229393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333132896388223940578819595 499699344582335910868229393)
        ·
          refine ⟨374774508436751933151172045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499699344582335910868229393 374774508436751933151172045)
          ·
            refine ⟨140540440663781974931689517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374774508436751933151172045 140540440663781974931689517)
            ·
              refine ⟨52702665248918240599383569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140540440663781974931689517 52702665248918240599383569)
              ·
                refine ⟨39526998936688680449537677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52702665248918240599383569 39526998936688680449537677)
                ·
                  refine ⟨14822624601258255168576629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39526998936688680449537677 14822624601258255168576629)
                  ·
                    refine ⟨1389621056367961422054059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14822624601258255168576629 1389621056367961422054059)
                    ·
                      rfl

theorem cell23_8118832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 3, 5].length) (baseStart_8118832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118832 prefixEnd_8118832 := by exact prefixLift 8118832
  have htrace : WordTrace (prefixWord ++ tailWord_8118832) baseStart_8118832 baseEnd_8118832 := by
    simpa [prefixWord, tailWord_8118832, baseEnd_8118832] using wordTrace_append hprefix tailTrace_8118832
  have hstable : (prefixWord ++ tailWord_8118832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118832).length < 2 ^ (prefixWord ++ tailWord_8118832).sum := by decide
  have hdescent : baseEnd_8118832 < baseStart_8118832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118839 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 1, 5, 2]
def baseStart_8118839 : Nat := 118140960795 + 8118839 * 2 ^ 59
def prefixEnd_8118839 : Nat := 4983230072969 + 3 ^ 40 * 8118839 * 2
def baseEnd_8118839 : Nat := 4168866763468465738774645

theorem tailTrace_8118839 : CollatzResearch.WordTrace tailWord_8118839 prefixEnd_8118839 4168866763468465738774645 := by
  unfold tailWord_8118839
  simp only [CollatzResearch.WordTrace]
  refine ⟨296118385433840365154455571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197412256955893576769637047 296118385433840365154455571)
  ·
    refine ⟨444177578150760547731683357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296118385433840365154455571 444177578150760547731683357)
    ·
      refine ⟨166566591806535205399381259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444177578150760547731683357 166566591806535205399381259)
      ·
        refine ⟨249849887709802808099071889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166566591806535205399381259 249849887709802808099071889)
        ·
          refine ⟨187387415782352106074303917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249849887709802808099071889 187387415782352106074303917)
          ·
            refine ⟨70270280918382039777863969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187387415782352106074303917 70270280918382039777863969)
            ·
              refine ⟨52702710688786529833397977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70270280918382039777863969 52702710688786529833397977)
              ·
                refine ⟨39527033016589897375048483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52702710688786529833397977 39527033016589897375048483)
                ·
                  refine ⟨59290549524884846062572725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39527033016589897375048483 59290549524884846062572725)
                  ·
                    refine ⟨5558489017957954318366193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59290549524884846062572725 5558489017957954318366193)
                    ·
                      refine ⟨4168866763468465738774645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5558489017957954318366193 4168866763468465738774645)
                      ·
                        rfl

theorem cell23_8118839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 5, 2].length) (baseStart_8118839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118839 prefixEnd_8118839 := by exact prefixLift 8118839
  have htrace : WordTrace (prefixWord ++ tailWord_8118839) baseStart_8118839 baseEnd_8118839 := by
    simpa [prefixWord, tailWord_8118839, baseEnd_8118839] using wordTrace_append hprefix tailTrace_8118839
  have hstable : (prefixWord ++ tailWord_8118839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118839).length < 2 ^ (prefixWord ++ tailWord_8118839).sum := by decide
  have hdescent : baseEnd_8118839 < baseStart_8118839 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118849 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 3, 5]
def baseStart_8118849 : Nat := 118140960795 + 8118849 * 2 ^ 59
def prefixEnd_8118849 : Nat := 4983230072969 + 3 ^ 40 * 8118849 * 2
def baseEnd_8118849 : Nat := 1389623966091670233216533

theorem tailTrace_8118849 : CollatzResearch.WordTrace tailWord_8118849 prefixEnd_8118849 1389623966091670233216533 := by
  unfold tailWord_8118849
  simp only [CollatzResearch.WordTrace]
  refine ⟨296118750163804136862319601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197412500109202757908213067 296118750163804136862319601)
  ·
    refine ⟨222089062622853102646739701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296118750163804136862319601 222089062622853102646739701)
    ·
      refine ⟨20820849620892478373131847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222089062622853102646739701 20820849620892478373131847)
      ·
        refine ⟨31231274431338717559697771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20820849620892478373131847 31231274431338717559697771)
        ·
          refine ⟨46846911647008076339546657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31231274431338717559697771 46846911647008076339546657)
          ·
            refine ⟨35135183735256057254659993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46846911647008076339546657 35135183735256057254659993)
            ·
              refine ⟨26351387801442042940994995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35135183735256057254659993 26351387801442042940994995)
              ·
                refine ⟨39527081702163064411492493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26351387801442042940994995 39527081702163064411492493)
                ·
                  refine ⟨14822655638311149154309685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39527081702163064411492493 14822655638311149154309685)
                  ·
                    refine ⟨1389623966091670233216533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14822655638311149154309685 1389623966091670233216533)
                    ·
                      rfl

theorem cell23_8118849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_8118849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118849 prefixEnd_8118849 := by exact prefixLift 8118849
  have htrace : WordTrace (prefixWord ++ tailWord_8118849) baseStart_8118849 baseEnd_8118849 := by
    simpa [prefixWord, tailWord_8118849, baseEnd_8118849] using wordTrace_append hprefix tailTrace_8118849
  have hstable : (prefixWord ++ tailWord_8118849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118849).length < 2 ^ (prefixWord ++ tailWord_8118849).sum := by decide
  have hdescent : baseEnd_8118849 < baseStart_8118849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118896 : List Nat := [2, 1, 1, 1, 7, 2, 1, 1, 1, 6]
def baseStart_8118896 : Nat := 118140960795 + 8118896 * 2 ^ 59
def prefixEnd_8118896 : Nat := 4983230072969 + 3 ^ 40 * 8118896 * 2
def baseEnd_8118896 : Nat := 1389632010621924005253961

theorem tailTrace_8118896 : CollatzResearch.WordTrace tailWord_8118896 prefixEnd_8118896 1389632010621924005253961 := by
  unfold tailWord_8118896
  simp only [CollatzResearch.WordTrace]
  refine ⟨148060232197316931944640271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197413642929755909259520361 148060232197316931944640271)
  ·
    refine ⟨222090348295975397916960407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148060232197316931944640271 222090348295975397916960407)
    ·
      refine ⟨333135522443963096875440611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222090348295975397916960407 333135522443963096875440611)
      ·
        refine ⟨499703283665944645313160917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333135522443963096875440611 499703283665944645313160917)
        ·
          refine ⟨11711795710920577624527209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 499703283665944645313160917 11711795710920577624527209)
          ·
            refine ⟨8783846783190433218395407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11711795710920577624527209 8783846783190433218395407)
            ·
              refine ⟨13175770174785649827593111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8783846783190433218395407 13175770174785649827593111)
              ·
                refine ⟨19763655262178474741389667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13175770174785649827593111 19763655262178474741389667)
                ·
                  refine ⟨29645482893267712112084501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19763655262178474741389667 29645482893267712112084501)
                  ·
                    refine ⟨1389632010621924005253961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29645482893267712112084501 1389632010621924005253961)
                    ·
                      rfl

theorem cell23_8118896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 1, 6].length) (baseStart_8118896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118896 prefixEnd_8118896 := by exact prefixLift 8118896
  have htrace : WordTrace (prefixWord ++ tailWord_8118896) baseStart_8118896 baseEnd_8118896 := by
    simpa [prefixWord, tailWord_8118896, baseEnd_8118896] using wordTrace_append hprefix tailTrace_8118896
  have hstable : (prefixWord ++ tailWord_8118896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118896).length < 2 ^ (prefixWord ++ tailWord_8118896).sum := by decide
  have hdescent : baseEnd_8118896 < baseStart_8118896 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118909 : List Nat := [1, 4, 1, 1, 5, 1, 1, 9]
def baseStart_8118909 : Nat := 118140960795 + 8118909 * 2 ^ 59
def prefixEnd_8118909 : Nat := 4983230072969 + 3 ^ 40 * 8118909 * 2
def baseEnd_8118909 : Nat := 154403803967195572774049

theorem tailTrace_8118909 : CollatzResearch.WordTrace tailWord_8118909 prefixEnd_8118909 154403803967195572774049 := by
  unfold tailWord_8118909
  simp only [CollatzResearch.WordTrace]
  refine ⟨296120938543586767109503781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197413959029057844739669187 296120938543586767109503781)
  ·
    refine ⟨55522675976922518833031959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296120938543586767109503781 55522675976922518833031959)
    ·
      refine ⟨83284013965383778249547939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55522675976922518833031959 83284013965383778249547939)
      ·
        refine ⟨124926020948075667374321909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83284013965383778249547939 124926020948075667374321909)
        ·
          refine ⟨11711814463882093816342679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124926020948075667374321909 11711814463882093816342679)
          ·
            refine ⟨17567721695823140724514019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11711814463882093816342679 17567721695823140724514019)
            ·
              refine ⟨26351582543734711086771029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17567721695823140724514019 26351582543734711086771029)
              ·
                refine ⟨154403803967195572774049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26351582543734711086771029 154403803967195572774049)
                ·
                  rfl

theorem cell23_8118909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 9].length) (baseStart_8118909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118909 prefixEnd_8118909 := by exact prefixLift 8118909
  have htrace : WordTrace (prefixWord ++ tailWord_8118909) baseStart_8118909 baseEnd_8118909 := by
    simpa [prefixWord, tailWord_8118909, baseEnd_8118909] using wordTrace_append hprefix tailTrace_8118909
  have hstable : (prefixWord ++ tailWord_8118909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118909).length < 2 ^ (prefixWord ++ tailWord_8118909).sum := by decide
  have hdescent : baseEnd_8118909 < baseStart_8118909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118919 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 3]
def baseStart_8118919 : Nat := 118140960795 + 8118919 * 2 ^ 59
def prefixEnd_8118919 : Nat := 4983230072969 + 3 ^ 40 * 8118919 * 2
def baseEnd_8118919 : Nat := 4168907841920825425774277

theorem tailTrace_8118919 : CollatzResearch.WordTrace tailWord_8118919 prefixEnd_8118919 4168907841920825425774277 := by
  unfold tailWord_8118919
  simp only [CollatzResearch.WordTrace]
  refine ⟨296121303273550538817367811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197414202182367025878245207 296121303273550538817367811)
  ·
    refine ⟨444181954910325808226051717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296121303273550538817367811 444181954910325808226051717)
    ·
      refine ⟨83284116545686089042384697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 444181954910325808226051717 83284116545686089042384697)
      ·
        refine ⟨62463087409264566781788523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83284116545686089042384697 62463087409264566781788523)
        ·
          refine ⟨93694631113896850172682785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62463087409264566781788523 93694631113896850172682785)
          ·
            refine ⟨70270973335422637629512089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93694631113896850172682785 70270973335422637629512089)
            ·
              refine ⟨52703230001566978222134067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70270973335422637629512089 52703230001566978222134067)
              ·
                refine ⟨79054845002350467333201101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52703230001566978222134067 79054845002350467333201101)
                ·
                  refine ⟨29645566875881425249950413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79054845002350467333201101 29645566875881425249950413)
                  ·
                    refine ⟨11117087578455534468731405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29645566875881425249950413 11117087578455534468731405)
                    ·
                      refine ⟨4168907841920825425774277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11117087578455534468731405 4168907841920825425774277)
                      ·
                        rfl

theorem cell23_8118919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_8118919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118919 prefixEnd_8118919 := by exact prefixLift 8118919
  have htrace : WordTrace (prefixWord ++ tailWord_8118919) baseStart_8118919 baseEnd_8118919 := by
    simpa [prefixWord, tailWord_8118919, baseEnd_8118919] using wordTrace_append hprefix tailTrace_8118919
  have hstable : (prefixWord ++ tailWord_8118919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118919).length < 2 ^ (prefixWord ++ tailWord_8118919).sum := by decide
  have hdescent : baseEnd_8118919 < baseStart_8118919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118929 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 1, 9, 2]
def baseStart_8118929 : Nat := 118140960795 + 8118929 * 2 ^ 59
def prefixEnd_8118929 : Nat := 4983230072969 + 3 ^ 40 * 8118929 * 2
def baseEnd_8118929 : Nat := 4168912976727370386649231

theorem tailTrace_8118929 : CollatzResearch.WordTrace tailWord_8118929 prefixEnd_8118929 4168912976727370386649231 := by
  unfold tailWord_8118929
  simp only [CollatzResearch.WordTrace]
  refine ⟨296121668003514310525231841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197414445335676207016821227 296121668003514310525231841)
  ·
    refine ⟨222091251002635732893923881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296121668003514310525231841 222091251002635732893923881)
    ·
      refine ⟨166568438251976799670442911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222091251002635732893923881 166568438251976799670442911)
      ·
        refine ⟨249852657377965199505664367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166568438251976799670442911 249852657377965199505664367)
        ·
          refine ⟨374778986066947799258496551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249852657377965199505664367 374778986066947799258496551)
          ·
            refine ⟨562168479100421698887744827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374778986066947799258496551 562168479100421698887744827)
            ·
              refine ⟨843252718650632548331617241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562168479100421698887744827 843252718650632548331617241)
              ·
                refine ⟨632439538987974411248712931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843252718650632548331617241 632439538987974411248712931)
                ·
                  refine ⟨948659308481961616873069397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632439538987974411248712931 948659308481961616873069397)
                  ·
                    refine ⟨5558550635636493848865641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 948659308481961616873069397 5558550635636493848865641)
                    ·
                      refine ⟨4168912976727370386649231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5558550635636493848865641 4168912976727370386649231)
                      ·
                        rfl

theorem cell23_8118929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 9, 2].length) (baseStart_8118929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118929 prefixEnd_8118929 := by exact prefixLift 8118929
  have htrace : WordTrace (prefixWord ++ tailWord_8118929) baseStart_8118929 baseEnd_8118929 := by
    simpa [prefixWord, tailWord_8118929, baseEnd_8118929] using wordTrace_append hprefix tailTrace_8118929
  have hstable : (prefixWord ++ tailWord_8118929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118929).length < 2 ^ (prefixWord ++ tailWord_8118929).sum := by decide
  have hdescent : baseEnd_8118929 < baseStart_8118929 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118936 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 4, 1, 3]
def baseStart_8118936 : Nat := 118140960795 + 8118936 * 2 ^ 59
def prefixEnd_8118936 : Nat := 4983230072969 + 3 ^ 40 * 8118936 * 2
def baseEnd_8118936 : Nat := 4168916571091951859261699

theorem tailTrace_8118936 : CollatzResearch.WordTrace tailWord_8118936 prefixEnd_8118936 4168916571091951859261699 := by
  unfold tailWord_8118936
  simp only [CollatzResearch.WordTrace]
  refine ⟨148060961657244475360368331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197414615542992633813824441 148060961657244475360368331)
  ·
    refine ⟨222091442485866713040552497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148060961657244475360368331 222091442485866713040552497)
    ·
      refine ⟨166568581864400034780414373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222091442485866713040552497 166568581864400034780414373)
      ·
        refine ⟨31231609099575006521327695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166568581864400034780414373 31231609099575006521327695)
        ·
          refine ⟨46847413649362509781991543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31231609099575006521327695 46847413649362509781991543)
          ·
            refine ⟨70271120474043764672987315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46847413649362509781991543 70271120474043764672987315)
            ·
              refine ⟨105406680711065647009480973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70271120474043764672987315 105406680711065647009480973)
              ·
                refine ⟨39527505266649617628555365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105406680711065647009480973 39527505266649617628555365)
                ·
                  refine ⟨7411407237496803305354131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39527505266649617628555365 7411407237496803305354131)
                  ·
                    refine ⟨11117110856245204958031197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7411407237496803305354131 11117110856245204958031197)
                    ·
                      refine ⟨4168916571091951859261699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11117110856245204958031197 4168916571091951859261699)
                      ·
                        rfl

theorem cell23_8118936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_8118936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118936 prefixEnd_8118936 := by exact prefixLift 8118936
  have htrace : WordTrace (prefixWord ++ tailWord_8118936) baseStart_8118936 baseEnd_8118936 := by
    simpa [prefixWord, tailWord_8118936, baseEnd_8118936] using wordTrace_append hprefix tailTrace_8118936
  have hstable : (prefixWord ++ tailWord_8118936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118936).length < 2 ^ (prefixWord ++ tailWord_8118936).sum := by decide
  have hdescent : baseEnd_8118936 < baseStart_8118936 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118963 : List Nat := [1, 1, 1, 2, 3, 4, 3, 2, 1, 3, 2]
def baseStart_8118963 : Nat := 118140960795 + 8118963 * 2 ^ 59
def prefixEnd_8118963 : Nat := 4983230072969 + 3 ^ 40 * 8118963 * 2
def baseEnd_8118963 : Nat := 4168930435069623253624075

theorem tailTrace_8118963 : CollatzResearch.WordTrace tailWord_8118963 prefixEnd_8118963 4168930435069623253624075 := by
  unfold tailWord_8118963
  simp only [CollatzResearch.WordTrace]
  refine ⟨296122908085391134331969543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197415272056927422887979695 296122908085391134331969543)
  ·
    refine ⟨444184362128086701497954315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296122908085391134331969543 444184362128086701497954315)
    ·
      refine ⟨666276543192130052246931473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444184362128086701497954315 666276543192130052246931473)
      ·
        refine ⟨499707407394097539185198605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666276543192130052246931473 499707407394097539185198605)
        ·
          refine ⟨187390277772786577194449477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 499707407394097539185198605 187390277772786577194449477)
          ·
            refine ⟨35135677082397483223959277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187390277772786577194449477 35135677082397483223959277)
            ·
              refine ⟨13175878905899056208984729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35135677082397483223959277 13175878905899056208984729)
              ·
                refine ⟨9881909179424292156738547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13175878905899056208984729 9881909179424292156738547)
                ·
                  refine ⟨14822863769136438235107821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9881909179424292156738547 14822863769136438235107821)
                  ·
                    refine ⟨5558573913426164338165433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14822863769136438235107821 5558573913426164338165433)
                    ·
                      refine ⟨4168930435069623253624075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5558573913426164338165433 4168930435069623253624075)
                      ·
                        rfl

theorem cell23_8118963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 3, 2].length) (baseStart_8118963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118963 prefixEnd_8118963 := by exact prefixLift 8118963
  have htrace : WordTrace (prefixWord ++ tailWord_8118963) baseStart_8118963 baseEnd_8118963 := by
    simpa [prefixWord, tailWord_8118963, baseEnd_8118963] using wordTrace_append hprefix tailTrace_8118963
  have hstable : (prefixWord ++ tailWord_8118963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118963).length < 2 ^ (prefixWord ++ tailWord_8118963).sum := by decide
  have hdescent : baseEnd_8118963 < baseStart_8118963 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8118976 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 3, 4, 2]
def baseStart_8118976 : Nat := 118140960795 + 8118976 * 2 ^ 59
def prefixEnd_8118976 : Nat := 4983230072969 + 3 ^ 40 * 8118976 * 2
def baseEnd_8118976 : Nat := 4168937110318131702761515

theorem tailTrace_8118976 : CollatzResearch.WordTrace tailWord_8118976 prefixEnd_8118976 4168937110318131702761515 := by
  unfold tailWord_8118976
  simp only [CollatzResearch.WordTrace]
  refine ⟨148061691117172018776096391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197415588156229358368128521 148061691117172018776096391)
  ·
    refine ⟨222092536675758028164144587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148061691117172018776096391 222092536675758028164144587)
    ·
      refine ⟨333138805013637042246216881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222092536675758028164144587 333138805013637042246216881)
      ·
        refine ⟨249854103760227781684662661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333138805013637042246216881 249854103760227781684662661)
        ·
          refine ⟨46847644455042709065874249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249854103760227781684662661 46847644455042709065874249)
          ·
            refine ⟨35135733341282031799405687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46847644455042709065874249 35135733341282031799405687)
            ·
              refine ⟨52703600011923047699108531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35135733341282031799405687 52703600011923047699108531)
              ·
                refine ⟨79055400017884571548662797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52703600011923047699108531 79055400017884571548662797)
                ·
                  refine ⟨29645775006706714330748549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79055400017884571548662797 29645775006706714330748549)
                  ·
                    refine ⟨5558582813757508937015353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29645775006706714330748549 5558582813757508937015353)
                    ·
                      refine ⟨4168937110318131702761515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5558582813757508937015353 4168937110318131702761515)
                      ·
                        rfl

theorem cell23_8118976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 3, 4, 2].length) (baseStart_8118976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8118976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8118976 prefixEnd_8118976 := by exact prefixLift 8118976
  have htrace : WordTrace (prefixWord ++ tailWord_8118976) baseStart_8118976 baseEnd_8118976 := by
    simpa [prefixWord, tailWord_8118976, baseEnd_8118976] using wordTrace_append hprefix tailTrace_8118976
  have hstable : (prefixWord ++ tailWord_8118976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8118976).length < 2 ^ (prefixWord ++ tailWord_8118976).sum := by decide
  have hdescent : baseEnd_8118976 < baseStart_8118976 := by decide
  rcases family_descends (prefixWord ++ tailWord_8118976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119016 : List Nat := [2, 1, 4, 1, 4, 1, 1, 2, 7]
def baseStart_8119016 : Nat := 118140960795 + 8119016 * 2 ^ 59
def prefixEnd_8119016 : Nat := 4983230072969 + 3 ^ 40 * 8119016 * 2
def baseEnd_8119016 : Nat := 463217516616034616251259

theorem tailTrace_8119016 : CollatzResearch.WordTrace tailWord_8119016 prefixEnd_8119016 463217516616034616251259 := by
  unfold tailWord_8119016
  simp only [CollatzResearch.WordTrace]
  refine ⟨148062420577099562191824451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197416560769466082922432601 148062420577099562191824451)
  ·
    refine ⟨222093630865649343287736677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148062420577099562191824451 222093630865649343287736677)
    ·
      refine ⟨41642555787309251866450627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222093630865649343287736677 41642555787309251866450627)
      ·
        refine ⟨62463833680963877799675941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41642555787309251866450627 62463833680963877799675941)
        ·
          refine ⟨11711968815180727087439239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62463833680963877799675941 11711968815180727087439239)
          ·
            refine ⟨17567953222771090631158859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11711968815180727087439239 17567953222771090631158859)
            ·
              refine ⟨26351929834156635946738289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17567953222771090631158859 26351929834156635946738289)
              ·
                refine ⟨19763947375617476960053717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26351929834156635946738289 19763947375617476960053717)
                ·
                  refine ⟨463217516616034616251259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19763947375617476960053717 463217516616034616251259)
                  ·
                    rfl

theorem cell23_8119016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 7].length) (baseStart_8119016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119016 prefixEnd_8119016 := by exact prefixLift 8119016
  have htrace : WordTrace (prefixWord ++ tailWord_8119016) baseStart_8119016 baseEnd_8119016 := by
    simpa [prefixWord, tailWord_8119016, baseEnd_8119016] using wordTrace_append hprefix tailTrace_8119016
  have hstable : (prefixWord ++ tailWord_8119016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119016).length < 2 ^ (prefixWord ++ tailWord_8119016).sum := by decide
  have hdescent : baseEnd_8119016 < baseStart_8119016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119089 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 10]
def baseStart_8119089 : Nat := 118140960795 + 8119089 * 2 ^ 59
def prefixEnd_8119089 : Nat := 4983230072969 + 3 ^ 40 * 8119089 * 2
def baseEnd_8119089 : Nat := 463221681514676640072055

theorem tailTrace_8119089 : CollatzResearch.WordTrace tailWord_8119089 prefixEnd_8119089 463221681514676640072055 := by
  unfold tailWord_8119089
  simp only [CollatzResearch.WordTrace]
  refine ⟨296127503682934657851056321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197418335788623105234037547 296127503682934657851056321)
  ·
    refine ⟨222095627762200993388292241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296127503682934657851056321 222095627762200993388292241)
    ·
      refine ⟨166571720821650745041219181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222095627762200993388292241 166571720821650745041219181)
      ·
        refine ⟨62464395308119029390457193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166571720821650745041219181 62464395308119029390457193)
        ·
          refine ⟨46848296481089272042842895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62464395308119029390457193 46848296481089272042842895)
          ·
            refine ⟨70272444721633908064264343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46848296481089272042842895 70272444721633908064264343)
            ·
              refine ⟨105408667082450862096396515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70272444721633908064264343 105408667082450862096396515)
              ·
                refine ⟨158113000623676293144594773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105408667082450862096396515 158113000623676293144594773)
                ·
                  refine ⟨463221681514676640072055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 158113000623676293144594773 463221681514676640072055)
                  ·
                    rfl

theorem cell23_8119089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 10].length) (baseStart_8119089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119089 prefixEnd_8119089 := by exact prefixLift 8119089
  have htrace : WordTrace (prefixWord ++ tailWord_8119089) baseStart_8119089 baseEnd_8119089 := by
    simpa [prefixWord, tailWord_8119089, baseEnd_8119089] using wordTrace_append hprefix tailTrace_8119089
  have hstable : (prefixWord ++ tailWord_8119089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119089).length < 2 ^ (prefixWord ++ tailWord_8119089).sum := by decide
  have hdescent : baseEnd_8119089 < baseStart_8119089 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119103 : List Nat := [1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 3]
def baseStart_8119103 : Nat := 118140960795 + 8119103 * 2 ^ 59
def prefixEnd_8119103 : Nat := 4983230072969 + 3 ^ 40 * 8119103 * 2
def baseEnd_8119103 : Nat := 4169002322361252705873431

theorem tailTrace_8119103 : CollatzResearch.WordTrace tailWord_8119103 prefixEnd_8119103 4169002322361252705873431 := by
  unfold tailWord_8119103
  simp only [CollatzResearch.WordTrace]
  refine ⟨296128014304883938242065963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197418676203255958828043975 296128014304883938242065963)
  ·
    refine ⟨444192021457325907363098945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296128014304883938242065963 444192021457325907363098945)
    ·
      refine ⟨333144016092994430522324209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444192021457325907363098945 333144016092994430522324209)
      ·
        refine ⟨249858012069745822891743157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333144016092994430522324209 249858012069745822891743157)
        ·
          refine ⟨23424188631538670896100921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249858012069745822891743157 23424188631538670896100921)
          ·
            refine ⟨17568141473654003172075691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23424188631538670896100921 17568141473654003172075691)
            ·
              refine ⟨26352212210481004758113537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17568141473654003172075691 26352212210481004758113537)
              ·
                refine ⟨19764159157860753568585153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26352212210481004758113537 19764159157860753568585153)
                ·
                  refine ⟨14823119368395565176438865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19764159157860753568585153 14823119368395565176438865)
                  ·
                    refine ⟨11117339526296673882329149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14823119368395565176438865 11117339526296673882329149)
                    ·
                      refine ⟨4169002322361252705873431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11117339526296673882329149 4169002322361252705873431)
                      ·
                        rfl

theorem cell23_8119103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_8119103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119103 prefixEnd_8119103 := by exact prefixLift 8119103
  have htrace : WordTrace (prefixWord ++ tailWord_8119103) baseStart_8119103 baseEnd_8119103 := by
    simpa [prefixWord, tailWord_8119103, baseEnd_8119103] using wordTrace_append hprefix tailTrace_8119103
  have hstable : (prefixWord ++ tailWord_8119103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119103).length < 2 ^ (prefixWord ++ tailWord_8119103).sum := by decide
  have hdescent : baseEnd_8119103 < baseStart_8119103 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119109 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 1, 2, 6]
def baseStart_8119109 : Nat := 118140960795 + 8119109 * 2 ^ 59
def prefixEnd_8119109 : Nat := 4983230072969 + 3 ^ 40 * 8119109 * 2
def baseEnd_8119109 : Nat := 4169005403245179682398403

theorem tailTrace_8119109 : CollatzResearch.WordTrace tailWord_8119109 prefixEnd_8119109 4169005403245179682398403 := by
  unfold tailWord_8119109
  simp only [CollatzResearch.WordTrace]
  refine ⟨296128233142862201266784381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197418822095241467511189587 296128233142862201266784381)
  ·
    refine ⟨111048087428573325475044143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296128233142862201266784381 111048087428573325475044143)
    ·
      refine ⟨166572131142859988212566215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111048087428573325475044143 166572131142859988212566215)
      ·
        refine ⟨249858196714289982318849323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166572131142859988212566215 249858196714289982318849323)
        ·
          refine ⟨374787295071434973478273985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249858196714289982318849323 374787295071434973478273985)
          ·
            refine ⟨281090471303576230108705489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374787295071434973478273985 281090471303576230108705489)
            ·
              refine ⟨210817853477682172581529117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281090471303576230108705489 210817853477682172581529117)
              ·
                refine ⟨79056695054130814718073419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210817853477682172581529117 79056695054130814718073419)
                ·
                  refine ⟨118585042581196222077110129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79056695054130814718073419 118585042581196222077110129)
                  ·
                    refine ⟨88938781935897166557832597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118585042581196222077110129 88938781935897166557832597)
                    ·
                      refine ⟨4169005403245179682398403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88938781935897166557832597 4169005403245179682398403)
                      ·
                        rfl

theorem cell23_8119109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_8119109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119109 prefixEnd_8119109 := by exact prefixLift 8119109
  have htrace : WordTrace (prefixWord ++ tailWord_8119109) baseStart_8119109 baseEnd_8119109 := by
    simpa [prefixWord, tailWord_8119109, baseEnd_8119109] using wordTrace_append hprefix tailTrace_8119109
  have hstable : (prefixWord ++ tailWord_8119109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119109).length < 2 ^ (prefixWord ++ tailWord_8119109).sum := by decide
  have hdescent : baseEnd_8119109 < baseStart_8119109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119136 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 3, 5]
def baseStart_8119136 : Nat := 118140960795 + 8119136 * 2 ^ 59
def prefixEnd_8119136 : Nat := 4983230072969 + 3 ^ 40 * 8119136 * 2
def baseEnd_8119136 : Nat := 1389673089074283692253593

theorem tailTrace_8119136 : CollatzResearch.WordTrace tailWord_8119136 prefixEnd_8119136 1389673089074283692253593 := by
  unfold tailWord_8119136
  simp only [CollatzResearch.WordTrace]
  refine ⟨148064608956882192439008631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197419478609176256585344841 148064608956882192439008631)
  ·
    refine ⟨222096913435323288658512947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148064608956882192439008631 222096913435323288658512947)
    ·
      refine ⟨333145370152984932987769421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222096913435323288658512947 333145370152984932987769421)
      ·
        refine ⟨124929513807369349870413533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333145370152984932987769421 124929513807369349870413533)
        ·
          refine ⟨46848567677763506201405075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124929513807369349870413533 46848567677763506201405075)
          ·
            refine ⟨70272851516645259302107613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46848567677763506201405075 70272851516645259302107613)
            ·
              refine ⟨26352319318741972238290355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70272851516645259302107613 26352319318741972238290355)
              ·
                refine ⟨39528478978112958357435533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26352319318741972238290355 39528478978112958357435533)
                ·
                  refine ⟨14823179616792359384038325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39528478978112958357435533 14823179616792359384038325)
                  ·
                    refine ⟨1389673089074283692253593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14823179616792359384038325 1389673089074283692253593)
                    ·
                      rfl

theorem cell23_8119136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 3, 5].length) (baseStart_8119136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119136 prefixEnd_8119136 := by exact prefixLift 8119136
  have htrace : WordTrace (prefixWord ++ tailWord_8119136) baseStart_8119136 baseEnd_8119136 := by
    simpa [prefixWord, tailWord_8119136, baseEnd_8119136] using wordTrace_append hprefix tailTrace_8119136
  have hstable : (prefixWord ++ tailWord_8119136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119136).length < 2 ^ (prefixWord ++ tailWord_8119136).sum := by decide
  have hdescent : baseEnd_8119136 < baseStart_8119136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119167 : List Nat := [1, 1, 2, 2, 1, 1, 8, 2, 1, 1, 3]
def baseStart_8119167 : Nat := 118140960795 + 8119167 * 2 ^ 59
def prefixEnd_8119167 : Nat := 4983230072969 + 3 ^ 40 * 8119167 * 2
def baseEnd_8119167 : Nat := 4169035185123140455473137

theorem tailTrace_8119167 : CollatzResearch.WordTrace tailWord_8119167 prefixEnd_8119167 4169035185123140455473137 := by
  unfold tailWord_8119167
  simp only [CollatzResearch.WordTrace]
  refine ⟨296130348576652077172395755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197420232384434718114930503 296130348576652077172395755)
  ·
    refine ⟨444195522864978115758593633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296130348576652077172395755 444195522864978115758593633)
    ·
      refine ⟨333146642148733586818945225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444195522864978115758593633 333146642148733586818945225)
      ·
        refine ⟨249859981611550190114208919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333146642148733586818945225 249859981611550190114208919)
        ·
          refine ⟨374789972417325285171313379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249859981611550190114208919 374789972417325285171313379)
          ·
            refine ⟨562184958625987927756970069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374789972417325285171313379 562184958625987927756970069)
            ·
              refine ⟨6588104983898296028401993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 562184958625987927756970069 6588104983898296028401993)
              ·
                refine ⟨4941078737923722021301495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6588104983898296028401993 4941078737923722021301495)
                ·
                  refine ⟨7411618106885583031952243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4941078737923722021301495 7411618106885583031952243)
                  ·
                    refine ⟨11117427160328374547928365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7411618106885583031952243 11117427160328374547928365)
                    ·
                      refine ⟨4169035185123140455473137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11117427160328374547928365 4169035185123140455473137)
                      ·
                        rfl

theorem cell23_8119167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 1, 1, 3].length) (baseStart_8119167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119167 prefixEnd_8119167 := by exact prefixLift 8119167
  have htrace : WordTrace (prefixWord ++ tailWord_8119167) baseStart_8119167 baseEnd_8119167 := by
    simpa [prefixWord, tailWord_8119167, baseEnd_8119167] using wordTrace_append hprefix tailTrace_8119167
  have hstable : (prefixWord ++ tailWord_8119167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119167).length < 2 ^ (prefixWord ++ tailWord_8119167).sum := by decide
  have hdescent : baseEnd_8119167 < baseStart_8119167 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119193 : List Nat := [1, 2, 1, 2, 1, 3, 1, 6, 1, 2, 3]
def baseStart_8119193 : Nat := 118140960795 + 8119193 * 2 ^ 59
def prefixEnd_8119193 : Nat := 4983230072969 + 3 ^ 40 * 8119193 * 2
def baseEnd_8119193 : Nat := 4169048535620157353748017

theorem tailTrace_8119193 : CollatzResearch.WordTrace tailWord_8119193 prefixEnd_8119193 4169048535620157353748017 := by
  unfold tailWord_8119193
  simp only [CollatzResearch.WordTrace]
  refine ⟨296131296874557883612842233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197420864583038589075228155 296131296874557883612842233)
  ·
    refine ⟨222098472655918412709631675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296131296874557883612842233 222098472655918412709631675)
    ·
      refine ⟨333147708983877619064447513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222098472655918412709631675 333147708983877619064447513)
      ·
        refine ⟨249860781737908214298335635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333147708983877619064447513 249860781737908214298335635)
        ·
          refine ⟨374791172606862321447503453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249860781737908214298335635 374791172606862321447503453)
          ·
            refine ⟨140546689727573370542813795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374791172606862321447503453 140546689727573370542813795)
            ·
              refine ⟨210820034591360055814220693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140546689727573370542813795 210820034591360055814220693)
              ·
                refine ⟨9882189121470002616291595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 210820034591360055814220693 9882189121470002616291595)
                ·
                  refine ⟨14823283682205003924437393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9882189121470002616291595 14823283682205003924437393)
                  ·
                    refine ⟨11117462761653752943328045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14823283682205003924437393 11117462761653752943328045)
                    ·
                      refine ⟨4169048535620157353748017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11117462761653752943328045 4169048535620157353748017)
                      ·
                        rfl

theorem cell23_8119193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 2, 3].length) (baseStart_8119193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119193 prefixEnd_8119193 := by exact prefixLift 8119193
  have htrace : WordTrace (prefixWord ++ tailWord_8119193) baseStart_8119193 baseEnd_8119193 := by
    simpa [prefixWord, tailWord_8119193, baseEnd_8119193] using wordTrace_append hprefix tailTrace_8119193
  have hstable : (prefixWord ++ tailWord_8119193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119193).length < 2 ^ (prefixWord ++ tailWord_8119193).sum := by decide
  have hdescent : baseEnd_8119193 < baseStart_8119193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119194 : List Nat := [3, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2]
def baseStart_8119194 : Nat := 118140960795 + 8119194 * 2 ^ 59
def prefixEnd_8119194 : Nat := 4983230072969 + 3 ^ 40 * 8119194 * 2
def baseEnd_8119194 : Nat := 4169049049100811849835513

theorem tailTrace_8119194 : CollatzResearch.WordTrace tailWord_8119194 prefixEnd_8119194 4169049049100811849835513 := by
  unfold tailWord_8119194
  simp only [CollatzResearch.WordTrace]
  refine ⟨74032833336888565195907159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197420888898369507189085757 74032833336888565195907159)
  ·
    refine ⟨111049250005332847793860739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74032833336888565195907159 111049250005332847793860739)
    ·
      refine ⟨166573875007999271690791109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111049250005332847793860739 166573875007999271690791109)
      ·
        refine ⟨31232601563999863442023333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166573875007999271690791109 31232601563999863442023333)
        ·
          refine ⟨5856112793249974395379375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31232601563999863442023333 5856112793249974395379375)
          ·
            refine ⟨8784169189874961593069063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5856112793249974395379375 8784169189874961593069063)
            ·
              refine ⟨13176253784812442389603595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8784169189874961593069063 13176253784812442389603595)
              ·
                refine ⟨19764380677218663584405393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13176253784812442389603595 19764380677218663584405393)
                ·
                  refine ⟨14823285507913997688304045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19764380677218663584405393 14823285507913997688304045)
                  ·
                    refine ⟨5558732065467749133114017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14823285507913997688304045 5558732065467749133114017)
                    ·
                      refine ⟨4169049049100811849835513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5558732065467749133114017 4169049049100811849835513)
                      ·
                        rfl

theorem cell23_8119194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_8119194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119194 prefixEnd_8119194 := by exact prefixLift 8119194
  have htrace : WordTrace (prefixWord ++ tailWord_8119194) baseStart_8119194 baseEnd_8119194 := by
    simpa [prefixWord, tailWord_8119194, baseEnd_8119194] using wordTrace_append hprefix tailTrace_8119194
  have hstable : (prefixWord ++ tailWord_8119194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119194).length < 2 ^ (prefixWord ++ tailWord_8119194).sum := by decide
  have hdescent : baseEnd_8119194 < baseStart_8119194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119217 : List Nat := [1, 2, 2, 4, 3, 2, 1, 2, 2, 4]
def baseStart_8119217 : Nat := 118140960795 + 8119217 * 2 ^ 59
def prefixEnd_8119217 : Nat := 4983230072969 + 3 ^ 40 * 8119217 * 2
def baseEnd_8119217 : Nat := 1389686953051955086615969

theorem tailTrace_8119217 : CollatzResearch.WordTrace tailWord_8119217 prefixEnd_8119217 1389686953051955086615969 := by
  unfold tailWord_8119217
  simp only [CollatzResearch.WordTrace]
  refine ⟨296132172226470935711715905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197421448150980623807810603 296132172226470935711715905)
  ·
    refine ⟨222099129169853201783786929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296132172226470935711715905 222099129169853201783786929)
    ·
      refine ⟨166574346877389901337840197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222099129169853201783786929 166574346877389901337840197)
      ·
        refine ⟨31232690039510606500845037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166574346877389901337840197 31232690039510606500845037)
        ·
          refine ⟨11712258764816477437816889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31232690039510606500845037 11712258764816477437816889)
          ·
            refine ⟨8784194073612358078362667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11712258764816477437816889 8784194073612358078362667)
            ·
              refine ⟨13176291110418537117544001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8784194073612358078362667 13176291110418537117544001)
              ·
                refine ⟨9882218332813902838158001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13176291110418537117544001 9882218332813902838158001)
                ·
                  refine ⟨7411663749610427128618501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9882218332813902838158001 7411663749610427128618501)
                  ·
                    refine ⟨1389686953051955086615969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7411663749610427128618501 1389686953051955086615969)
                    ·
                      rfl

theorem cell23_8119217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_8119217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119217 prefixEnd_8119217 := by exact prefixLift 8119217
  have htrace : WordTrace (prefixWord ++ tailWord_8119217) baseStart_8119217 baseEnd_8119217 := by
    simpa [prefixWord, tailWord_8119217, baseEnd_8119217] using wordTrace_append hprefix tailTrace_8119217
  have hstable : (prefixWord ++ tailWord_8119217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119217).length < 2 ^ (prefixWord ++ tailWord_8119217).sum := by decide
  have hdescent : baseEnd_8119217 < baseStart_8119217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119333 : List Nat := [1, 3, 1, 2, 2, 2, 1, 4, 2, 5]
def baseStart_8119333 : Nat := 118140960795 + 8119333 * 2 ^ 59
def prefixEnd_8119333 : Nat := 4983230072969 + 3 ^ 40 * 8119333 * 2
def baseEnd_8119333 : Nat := 1389706807637262268665791

theorem tailTrace_8119333 : CollatzResearch.WordTrace tailWord_8119333 prefixEnd_8119333 1389706807637262268665791 := by
  unfold tailWord_8119333
  simp only [CollatzResearch.WordTrace]
  refine ⟨296136403094050687522938653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197424268729367125015292435 296136403094050687522938653)
  ·
    refine ⟨111051151160269007821101995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296136403094050687522938653 111051151160269007821101995)
    ·
      refine ⟨166576726740403511731652993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111051151160269007821101995 166576726740403511731652993)
      ·
        refine ⟨124932545055302633798739745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166576726740403511731652993 124932545055302633798739745)
        ·
          refine ⟨93699408791476975349054809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124932545055302633798739745 93699408791476975349054809)
          ·
            refine ⟨70274556593607731511791107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93699408791476975349054809 70274556593607731511791107)
            ·
              refine ⟨105411834890411597267686661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70274556593607731511791107 105411834890411597267686661)
              ·
                refine ⟨19764719041952174487691249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105411834890411597267686661 19764719041952174487691249)
                ·
                  refine ⟨14823539281464130865768437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19764719041952174487691249 14823539281464130865768437)
                  ·
                    refine ⟨1389706807637262268665791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14823539281464130865768437 1389706807637262268665791)
                    ·
                      rfl

theorem cell23_8119333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_8119333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119333 prefixEnd_8119333 := by exact prefixLift 8119333
  have htrace : WordTrace (prefixWord ++ tailWord_8119333) baseStart_8119333 baseEnd_8119333 := by
    simpa [prefixWord, tailWord_8119333, baseEnd_8119333] using wordTrace_append hprefix tailTrace_8119333
  have hstable : (prefixWord ++ tailWord_8119333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119333).length < 2 ^ (prefixWord ++ tailWord_8119333).sum := by decide
  have hdescent : baseEnd_8119333 < baseStart_8119333 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119370 : List Nat := [3, 1, 2, 1, 1, 2, 5, 1, 2, 1, 4]
def baseStart_8119370 : Nat := 118140960795 + 8119370 * 2 ^ 59
def prefixEnd_8119370 : Nat := 4983230072969 + 3 ^ 40 * 8119370 * 2
def baseEnd_8119370 : Nat := 4169139421696003161234703

theorem tailTrace_8119370 : CollatzResearch.WordTrace tailWord_8119370 prefixEnd_8119370 4169139421696003161234703 := by
  unfold tailWord_8119370
  simp only [CollatzResearch.WordTrace]
  refine ⟨74034438148729160710508891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197425168396611095228023709 74034438148729160710508891)
  ·
    refine ⟨111051657223093741065763337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74034438148729160710508891 111051657223093741065763337)
    ·
      refine ⟨83288742917320305799322503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111051657223093741065763337 83288742917320305799322503)
      ·
        refine ⟨124933114375980458698983755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83288742917320305799322503 124933114375980458698983755)
        ·
          refine ⟨187399671563970688048475633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124933114375980458698983755 187399671563970688048475633)
          ·
            refine ⟨140549753672978016036356725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187399671563970688048475633 140549753672978016036356725)
            ·
              refine ⟨13176539406841689003408443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140549753672978016036356725 13176539406841689003408443)
              ·
                refine ⟨19764809110262533505112665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13176539406841689003408443 19764809110262533505112665)
                ·
                  refine ⟨14823606832696900128834499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19764809110262533505112665 14823606832696900128834499)
                  ·
                    refine ⟨22235410249045350193251749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14823606832696900128834499 22235410249045350193251749)
                    ·
                      refine ⟨4169139421696003161234703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22235410249045350193251749 4169139421696003161234703)
                      ·
                        rfl

theorem cell23_8119370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_8119370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119370 prefixEnd_8119370 := by exact prefixLift 8119370
  have htrace : WordTrace (prefixWord ++ tailWord_8119370) baseStart_8119370 baseEnd_8119370 := by
    simpa [prefixWord, tailWord_8119370, baseEnd_8119370] using wordTrace_append hprefix tailTrace_8119370
  have hstable : (prefixWord ++ tailWord_8119370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119370).length < 2 ^ (prefixWord ++ tailWord_8119370).sum := by decide
  have hdescent : baseEnd_8119370 < baseStart_8119370 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119397 : List Nat := [1, 3, 1, 3, 2, 1, 1, 6, 1, 4]
def baseStart_8119397 : Nat := 118140960795 + 8119397 * 2 ^ 59
def prefixEnd_8119397 : Nat := 4983230072969 + 3 ^ 40 * 8119397 * 2
def baseEnd_8119397 : Nat := 1389717761891224851865693

theorem tailTrace_8119397 : CollatzResearch.WordTrace tailWord_8119397 prefixEnd_8119397 1389717761891224851865693 := by
  unfold tailWord_8119397
  simp only [CollatzResearch.WordTrace]
  refine ⟨296138737365818826453268445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197425824910545884302178963 296138737365818826453268445)
  ·
    refine ⟨111052026512182059919975667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296138737365818826453268445 111052026512182059919975667)
    ·
      refine ⟨166578039768273089879963501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111052026512182059919975667 166578039768273089879963501)
      ·
        refine ⟨62466764913102408704986313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166578039768273089879963501 62466764913102408704986313)
        ·
          refine ⟨46850073684826806528739735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62466764913102408704986313 46850073684826806528739735)
          ·
            refine ⟨70275110527240209793109603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46850073684826806528739735 70275110527240209793109603)
            ·
              refine ⟨105412665790860314689664405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70275110527240209793109603 105412665790860314689664405)
              ·
                refine ⟨4941218708946577251078019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105412665790860314689664405 4941218708946577251078019)
                ·
                  refine ⟨7411828063419865876617029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4941218708946577251078019 7411828063419865876617029)
                  ·
                    refine ⟨1389717761891224851865693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7411828063419865876617029 1389717761891224851865693)
                    ·
                      rfl

theorem cell23_8119397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 1, 4].length) (baseStart_8119397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119397 prefixEnd_8119397 := by exact prefixLift 8119397
  have htrace : WordTrace (prefixWord ++ tailWord_8119397) baseStart_8119397 baseEnd_8119397 := by
    simpa [prefixWord, tailWord_8119397, baseEnd_8119397] using wordTrace_append hprefix tailTrace_8119397
  have hstable : (prefixWord ++ tailWord_8119397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119397).length < 2 ^ (prefixWord ++ tailWord_8119397).sum := by decide
  have hdescent : baseEnd_8119397 < baseStart_8119397 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119447 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 4, 3, 2]
def baseStart_8119447 : Nat := 118140960795 + 8119447 * 2 ^ 59
def prefixEnd_8119447 : Nat := 4983230072969 + 3 ^ 40 * 8119447 * 2
def baseEnd_8119447 : Nat := 4169178959706399359971849

theorem tailTrace_8119447 : CollatzResearch.WordTrace tailWord_8119447 prefixEnd_8119447 4169178959706399359971849 := by
  unfold tailWord_8119447
  simp only [CollatzResearch.WordTrace]
  refine ⟨296140561015637684992588595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197427040677091789995059063 296140561015637684992588595)
  ·
    refine ⟨444210841523456527488882893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296140561015637684992588595 444210841523456527488882893)
    ·
      refine ⟨166579065571296197808331085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444210841523456527488882893 166579065571296197808331085)
      ·
        refine ⟨62467149589236074178124157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166579065571296197808331085 62467149589236074178124157)
        ·
          refine ⟨23425181095963527816796559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62467149589236074178124157 23425181095963527816796559)
          ·
            refine ⟨35137771643945291725194839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23425181095963527816796559 35137771643945291725194839)
            ·
              refine ⟨52706657465917937587792259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35137771643945291725194839 52706657465917937587792259)
              ·
                refine ⟨79059986198876906381688389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52706657465917937587792259 79059986198876906381688389)
                ·
                  refine ⟨14823747412289419946566573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79059986198876906381688389 14823747412289419946566573)
                  ·
                    refine ⟨5558905279608532479962465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14823747412289419946566573 5558905279608532479962465)
                    ·
                      refine ⟨4169178959706399359971849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5558905279608532479962465 4169178959706399359971849)
                      ·
                        rfl

theorem cell23_8119447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_8119447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119447 prefixEnd_8119447 := by exact prefixLift 8119447
  have htrace : WordTrace (prefixWord ++ tailWord_8119447) baseStart_8119447 baseEnd_8119447 := by
    simpa [prefixWord, tailWord_8119447, baseEnd_8119447] using wordTrace_append hprefix tailTrace_8119447
  have hstable : (prefixWord ++ tailWord_8119447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119447).length < 2 ^ (prefixWord ++ tailWord_8119447).sum := by decide
  have hdescent : baseEnd_8119447 < baseStart_8119447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119503 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 6]
def baseStart_8119503 : Nat := 118140960795 + 8119503 * 2 ^ 59
def prefixEnd_8119503 : Nat := 4983230072969 + 3 ^ 40 * 8119503 * 2
def baseEnd_8119503 : Nat := 4169207714623051140871591

theorem tailTrace_8119503 : CollatzResearch.WordTrace tailWord_8119503 prefixEnd_8119503 4169207714623051140871591 := by
  unfold tailWord_8119503
  simp only [CollatzResearch.WordTrace]
  refine ⟨296142603503434806556627163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197428402335623204371084775 296142603503434806556627163)
  ·
    refine ⟨444213905255152209834940745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296142603503434806556627163 444213905255152209834940745)
    ·
      refine ⟨333160428941364157376205559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444213905255152209834940745 333160428941364157376205559)
      ·
        refine ⟨499740643412046236064308339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333160428941364157376205559 499740643412046236064308339)
        ·
          refine ⟨749610965118069354096462509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499740643412046236064308339 749610965118069354096462509)
          ·
            refine ⟨281104111919276007786173441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 749610965118069354096462509 281104111919276007786173441)
            ·
              refine ⟨210828083939457005839630081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281104111919276007786173441 210828083939457005839630081)
              ·
                refine ⟨158121062954592754379722561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210828083939457005839630081 158121062954592754379722561)
                ·
                  refine ⟨118590797215944565784791921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158121062954592754379722561 118590797215944565784791921)
                  ·
                    refine ⟨88943097911958424338593941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118590797215944565784791921 88943097911958424338593941)
                    ·
                      refine ⟨4169207714623051140871591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88943097911958424338593941 4169207714623051140871591)
                      ·
                        rfl

theorem cell23_8119503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_8119503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119503 prefixEnd_8119503 := by exact prefixLift 8119503
  have htrace : WordTrace (prefixWord ++ tailWord_8119503) baseStart_8119503 baseEnd_8119503 := by
    simpa [prefixWord, tailWord_8119503, baseEnd_8119503] using wordTrace_append hprefix tailTrace_8119503
  have hstable : (prefixWord ++ tailWord_8119503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119503).length < 2 ^ (prefixWord ++ tailWord_8119503).sum := by decide
  have hdescent : baseEnd_8119503 < baseStart_8119503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119548 : List Nat := [2, 2, 2, 1, 6, 1, 2, 1, 1, 2, 3]
def baseStart_8119548 : Nat := 118140960795 + 8119548 * 2 ^ 59
def prefixEnd_8119548 : Nat := 4983230072969 + 3 ^ 40 * 8119548 * 2
def baseEnd_8119548 : Nat := 4169230821252503464808885

theorem tailTrace_8119548 : CollatzResearch.WordTrace tailWord_8119548 prefixEnd_8119548 4169230821252503464808885 := by
  unfold tailWord_8119548
  simp only [CollatzResearch.WordTrace]
  refine ⟨148072122394135889621007649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197429496525514519494676865 148072122394135889621007649)
  ·
    refine ⟨111054091795601917215755737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148072122394135889621007649 111054091795601917215755737)
    ·
      refine ⟨83290568846701437911816803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111054091795601917215755737 83290568846701437911816803)
      ·
        refine ⟨124935853270052156867725205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83290568846701437911816803 124935853270052156867725205)
        ·
          refine ⟨5856368122033694853174619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 124935853270052156867725205 5856368122033694853174619)
          ·
            refine ⟨8784552183050542279761929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5856368122033694853174619 8784552183050542279761929)
            ·
              refine ⟨6588414137287906709821447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8784552183050542279761929 6588414137287906709821447)
              ·
                refine ⟨9882621205931860064732171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6588414137287906709821447 9882621205931860064732171)
                ·
                  refine ⟨14823931808897790097098257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9882621205931860064732171 14823931808897790097098257)
                  ·
                    refine ⟨11117948856673342572823693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14823931808897790097098257 11117948856673342572823693)
                    ·
                      refine ⟨4169230821252503464808885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11117948856673342572823693 4169230821252503464808885)
                      ·
                        rfl

theorem cell23_8119548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_8119548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119548 prefixEnd_8119548 := by exact prefixLift 8119548
  have htrace : WordTrace (prefixWord ++ tailWord_8119548) baseStart_8119548 baseEnd_8119548 := by
    simpa [prefixWord, tailWord_8119548, baseEnd_8119548] using wordTrace_append hprefix tailTrace_8119548
  have hstable : (prefixWord ++ tailWord_8119548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119548).length < 2 ^ (prefixWord ++ tailWord_8119548).sum := by decide
  have hdescent : baseEnd_8119548 < baseStart_8119548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119657 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 3, 6, 2]
def baseStart_8119657 : Nat := 118140960795 + 8119657 * 2 ^ 59
def prefixEnd_8119657 : Nat := 4983230072969 + 3 ^ 40 * 8119657 * 2
def baseEnd_8119657 : Nat := 4169286790643843538345883

theorem tailTrace_8119657 : CollatzResearch.WordTrace tailWord_8119657 prefixEnd_8119657 4169286790643843538345883 := by
  unfold tailWord_8119657
  simp only [CollatzResearch.WordTrace]
  refine ⟨296148220344876890857733225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197432146896584593905155483 296148220344876890857733225)
  ·
    refine ⟨222111165258657668143299919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296148220344876890857733225 222111165258657668143299919)
    ·
      refine ⟨333166747887986502214949879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222111165258657668143299919 333166747887986502214949879)
      ·
        refine ⟨499750121831979753322424819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333166747887986502214949879 499750121831979753322424819)
        ·
          refine ⟨749625182747969629983637229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499750121831979753322424819 749625182747969629983637229)
          ·
            refine ⟨281109443530488611243863961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 749625182747969629983637229 281109443530488611243863961)
            ·
              refine ⟨210832082647866458432897971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281109443530488611243863961 210832082647866458432897971)
              ·
                refine ⟨316248123971799687649346957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210832082647866458432897971 316248123971799687649346957)
                ·
                  refine ⟨118593046489424882868505109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316248123971799687649346957 118593046489424882868505109)
                  ·
                    refine ⟨5559049054191791384461177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118593046489424882868505109 5559049054191791384461177)
                    ·
                      refine ⟨4169286790643843538345883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5559049054191791384461177 4169286790643843538345883)
                      ·
                        rfl

theorem cell23_8119657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 6, 2].length) (baseStart_8119657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119657 prefixEnd_8119657 := by exact prefixLift 8119657
  have htrace : WordTrace (prefixWord ++ tailWord_8119657) baseStart_8119657 baseEnd_8119657 := by
    simpa [prefixWord, tailWord_8119657, baseEnd_8119657] using wordTrace_append hprefix tailTrace_8119657
  have hstable : (prefixWord ++ tailWord_8119657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119657).length < 2 ^ (prefixWord ++ tailWord_8119657).sum := by decide
  have hdescent : baseEnd_8119657 < baseStart_8119657 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119680 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 8]
def baseStart_8119680 : Nat := 118140960795 + 8119680 * 2 ^ 59
def prefixEnd_8119680 : Nat := 4983230072969 + 3 ^ 40 * 8119680 * 2
def baseEnd_8119680 : Nat := 463255400077655216484253

theorem tailTrace_8119680 : CollatzResearch.WordTrace tailWord_8119680 prefixEnd_8119680 463255400077655216484253 := by
  unfold tailWord_8119680
  simp only [CollatzResearch.WordTrace]
  refine ⟨148074529611896782892910247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197432706149195710523880329 148074529611896782892910247)
  ·
    refine ⟨222111794417845174339365371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148074529611896782892910247 222111794417845174339365371)
    ·
      refine ⟨333167691626767761509048057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222111794417845174339365371 333167691626767761509048057)
      ·
        refine ⟨249875768720075821131786043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333167691626767761509048057 249875768720075821131786043)
        ·
          refine ⟨374813653080113731697679065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249875768720075821131786043 374813653080113731697679065)
          ·
            refine ⟨281110239810085298773259299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374813653080113731697679065 281110239810085298773259299)
            ·
              refine ⟨421665359715127948159888949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281110239810085298773259299 421665359715127948159888949)
              ·
                refine ⟨39531127473293245139989589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 421665359715127948159888949 39531127473293245139989589)
                ·
                  refine ⟨463255400077655216484253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39531127473293245139989589 463255400077655216484253)
                  ·
                    rfl

theorem cell23_8119680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 8].length) (baseStart_8119680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119680 prefixEnd_8119680 := by exact prefixLift 8119680
  have htrace : WordTrace (prefixWord ++ tailWord_8119680) baseStart_8119680 baseEnd_8119680 := by
    simpa [prefixWord, tailWord_8119680, baseEnd_8119680] using wordTrace_append hprefix tailTrace_8119680
  have hstable : (prefixWord ++ tailWord_8119680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119680).length < 2 ^ (prefixWord ++ tailWord_8119680).sum := by decide
  have hdescent : baseEnd_8119680 < baseStart_8119680 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119708 : List Nat := [2, 2, 3, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_8119708 : Nat := 118140960795 + 8119708 * 2 ^ 59
def prefixEnd_8119708 : Nat := 4983230072969 + 3 ^ 40 * 8119708 * 2
def baseEnd_8119708 : Nat := 4169312978157222838808149

theorem tailTrace_8119708 : CollatzResearch.WordTrace tailWord_8119708 prefixEnd_8119708 4169312978157222838808149 := by
  unfold tailWord_8119708
  simp only [CollatzResearch.WordTrace]
  refine ⟨148075040233846063283919889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197433386978461417711893185 148075040233846063283919889)
  ·
    refine ⟨111056280175384547462939917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148075040233846063283919889 111056280175384547462939917)
    ·
      refine ⟨41646105065769205298602469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111056280175384547462939917 41646105065769205298602469)
      ·
        refine ⟨7808644699831725993487963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41646105065769205298602469 7808644699831725993487963)
        ·
          refine ⟨11712967049747588990231945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7808644699831725993487963 11712967049747588990231945)
          ·
            refine ⟨8784725287310691742673959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11712967049747588990231945 8784725287310691742673959)
            ·
              refine ⟨13177087930966037614010939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8784725287310691742673959 13177087930966037614010939)
              ·
                refine ⟨19765631896449056421016409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13177087930966037614010939 19765631896449056421016409)
                ·
                  refine ⟨14824223922336792315762307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19765631896449056421016409 14824223922336792315762307)
                  ·
                    refine ⟨22236335883505188473643461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14824223922336792315762307 22236335883505188473643461)
                    ·
                      refine ⟨4169312978157222838808149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22236335883505188473643461 4169312978157222838808149)
                      ·
                        rfl

theorem cell23_8119708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_8119708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119708 prefixEnd_8119708 := by exact prefixLift 8119708
  have htrace : WordTrace (prefixWord ++ tailWord_8119708) baseStart_8119708 baseEnd_8119708 := by
    simpa [prefixWord, tailWord_8119708, baseEnd_8119708] using wordTrace_append hprefix tailTrace_8119708
  have hstable : (prefixWord ++ tailWord_8119708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119708).length < 2 ^ (prefixWord ++ tailWord_8119708).sum := by decide
  have hdescent : baseEnd_8119708 < baseStart_8119708 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119711 : List Nat := [1, 1, 2, 5, 1, 4, 1, 1, 2, 2, 3]
def baseStart_8119711 : Nat := 118140960795 + 8119711 * 2 ^ 59
def prefixEnd_8119711 : Nat := 4983230072969 + 3 ^ 40 * 8119711 * 2
def baseEnd_8119711 : Nat := 4169314518599186327070635

theorem tailTrace_8119711 : CollatzResearch.WordTrace tailWord_8119711 prefixEnd_8119711 4169314518599186327070635 := by
  unfold tailWord_8119711
  simp only [CollatzResearch.WordTrace]
  refine ⟨296150189886681258080198987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197433459924454172053465991 296150189886681258080198987)
  ·
    refine ⟨444225284830021887120298481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296150189886681258080198987 444225284830021887120298481)
    ·
      refine ⟨333168963622516415340223861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444225284830021887120298481 333168963622516415340223861)
      ·
        refine ⟨31234590339610913938145987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 333168963622516415340223861 31234590339610913938145987)
        ·
          refine ⟨46851885509416370907218981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31234590339610913938145987 46851885509416370907218981)
          ·
            refine ⟨8784728533015569545103559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46851885509416370907218981 8784728533015569545103559)
            ·
              refine ⟨13177092799523354317655339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8784728533015569545103559 13177092799523354317655339)
              ·
                refine ⟨19765639199285031476483009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13177092799523354317655339 19765639199285031476483009)
                ·
                  refine ⟨14824229399463773607362257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19765639199285031476483009 14824229399463773607362257)
                  ·
                    refine ⟨11118172049597830205521693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14824229399463773607362257 11118172049597830205521693)
                    ·
                      refine ⟨4169314518599186327070635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11118172049597830205521693 4169314518599186327070635)
                      ·
                        rfl

theorem cell23_8119711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_8119711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119711 prefixEnd_8119711 := by exact prefixLift 8119711
  have htrace : WordTrace (prefixWord ++ tailWord_8119711) baseStart_8119711 baseEnd_8119711 := by
    simpa [prefixWord, tailWord_8119711, baseEnd_8119711] using wordTrace_append hprefix tailTrace_8119711
  have hstable : (prefixWord ++ tailWord_8119711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119711).length < 2 ^ (prefixWord ++ tailWord_8119711).sum := by decide
  have hdescent : baseEnd_8119711 < baseStart_8119711 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119741 : List Nat := [1, 4, 1, 2, 2, 1, 4, 1, 3, 1, 3]
def baseStart_8119741 : Nat := 118140960795 + 8119741 * 2 ^ 59
def prefixEnd_8119741 : Nat := 4983230072969 + 3 ^ 40 * 8119741 * 2
def baseEnd_8119741 : Nat := 4169329923018821209695497

theorem tailTrace_8119741 : CollatzResearch.WordTrace tailWord_8119741 prefixEnd_8119741 4169329923018821209695497 := by
  unfold tailWord_8119741
  simp only [CollatzResearch.WordTrace]
  refine ⟨296151284076572573203791077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197434189384381715469194051 296151284076572573203791077)
  ·
    refine ⟨55528365764357357475710827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296151284076572573203791077 55528365764357357475710827)
    ·
      refine ⟨83292548646536036213566241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55528365764357357475710827 83292548646536036213566241)
      ·
        refine ⟨62469411484902027160174681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83292548646536036213566241 62469411484902027160174681)
        ·
          refine ⟨46852058613676520370131011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62469411484902027160174681 46852058613676520370131011)
          ·
            refine ⟨70278087920514780555196517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46852058613676520370131011 70278087920514780555196517)
            ·
              refine ⟨13177141485096521354099347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70278087920514780555196517 13177141485096521354099347)
              ·
                refine ⟨19765712227644782031149021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13177141485096521354099347 19765712227644782031149021)
                ·
                  refine ⟨7412142085366793261680883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19765712227644782031149021 7412142085366793261680883)
                  ·
                    refine ⟨11118213128050189892521325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7412142085366793261680883 11118213128050189892521325)
                    ·
                      refine ⟨4169329923018821209695497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11118213128050189892521325 4169329923018821209695497)
                      ·
                        rfl

theorem cell23_8119741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_8119741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119741 prefixEnd_8119741 := by exact prefixLift 8119741
  have htrace : WordTrace (prefixWord ++ tailWord_8119741) baseStart_8119741 baseEnd_8119741 := by
    simpa [prefixWord, tailWord_8119741, baseEnd_8119741] using wordTrace_append hprefix tailTrace_8119741
  have hstable : (prefixWord ++ tailWord_8119741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119741).length < 2 ^ (prefixWord ++ tailWord_8119741).sum := by decide
  have hdescent : baseEnd_8119741 < baseStart_8119741 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119747 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 4]
def baseStart_8119747 : Nat := 118140960795 + 8119747 * 2 ^ 59
def prefixEnd_8119747 : Nat := 4983230072969 + 3 ^ 40 * 8119747 * 2
def baseEnd_8119747 : Nat := 4169333003902748186220469

theorem tailTrace_8119747 : CollatzResearch.WordTrace tailWord_8119747 prefixEnd_8119747 4169333003902748186220469 := by
  unfold tailWord_8119747
  simp only [CollatzResearch.WordTrace]
  refine ⟨296151502914550836228509495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197434335276367224152339663 296151502914550836228509495)
  ·
    refine ⟨444227254371826254342764243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296151502914550836228509495 444227254371826254342764243)
    ·
      refine ⟨666340881557739381514146365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444227254371826254342764243 666340881557739381514146365)
      ·
        refine ⟨249877830584152268067804887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 666340881557739381514146365 249877830584152268067804887)
        ·
          refine ⟨374816745876228402101707331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249877830584152268067804887 374816745876228402101707331)
          ·
            refine ⟨562225118814342603152560997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374816745876228402101707331 562225118814342603152560997)
            ·
              refine ⟨105417209777689238091105187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 562225118814342603152560997 105417209777689238091105187)
              ·
                refine ⟨158125814666533857136657781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105417209777689238091105187 158125814666533857136657781)
                ·
                  refine ⟨14824295124987549106561667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158125814666533857136657781 14824295124987549106561667)
                  ·
                    refine ⟨22236442687481323659842501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14824295124987549106561667 22236442687481323659842501)
                    ·
                      refine ⟨4169333003902748186220469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22236442687481323659842501 4169333003902748186220469)
                      ·
                        rfl

theorem cell23_8119747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_8119747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119747 prefixEnd_8119747 := by exact prefixLift 8119747
  have htrace : WordTrace (prefixWord ++ tailWord_8119747) baseStart_8119747 baseEnd_8119747 := by
    simpa [prefixWord, tailWord_8119747, baseEnd_8119747] using wordTrace_append hprefix tailTrace_8119747
  have hstable : (prefixWord ++ tailWord_8119747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119747).length < 2 ^ (prefixWord ++ tailWord_8119747).sum := by decide
  have hdescent : baseEnd_8119747 < baseStart_8119747 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119767 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 3]
def baseStart_8119767 : Nat := 118140960795 + 8119767 * 2 ^ 59
def prefixEnd_8119767 : Nat := 4983230072969 + 3 ^ 40 * 8119767 * 2
def baseEnd_8119767 : Nat := 4169343273515838107970377

theorem tailTrace_8119767 : CollatzResearch.WordTrace tailWord_8119767 prefixEnd_8119767 4169343273515838107970377 := by
  unfold tailWord_8119767
  simp only [CollatzResearch.WordTrace]
  refine ⟨296152232374478379644237555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197434821582985586429491703 296152232374478379644237555)
  ·
    refine ⟨444228348561717569466356333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296152232374478379644237555 444228348561717569466356333)
    ·
      refine ⟨166585630710644088549883625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444228348561717569466356333 166585630710644088549883625)
      ·
        refine ⟨124939223032983066412412719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166585630710644088549883625 124939223032983066412412719)
        ·
          refine ⟨187408834549474599618619079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124939223032983066412412719 187408834549474599618619079)
          ·
            refine ⟨281113251824211899427928619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187408834549474599618619079 281113251824211899427928619)
            ·
              refine ⟨421669877736317849141892929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281113251824211899427928619 421669877736317849141892929)
              ·
                refine ⟨316252408302238386856419697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421669877736317849141892929 316252408302238386856419697)
                ·
                  refine ⟨237189306226678790142314773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316252408302238386856419697 237189306226678790142314773)
                  ·
                    refine ⟨11118248729375568287921005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 237189306226678790142314773 11118248729375568287921005)
                    ·
                      refine ⟨4169343273515838107970377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11118248729375568287921005 4169343273515838107970377)
                      ·
                        rfl

theorem cell23_8119767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_8119767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119767 prefixEnd_8119767 := by exact prefixLift 8119767
  have htrace : WordTrace (prefixWord ++ tailWord_8119767) baseStart_8119767 baseEnd_8119767 := by
    simpa [prefixWord, tailWord_8119767, baseEnd_8119767] using wordTrace_append hprefix tailTrace_8119767
  have hstable : (prefixWord ++ tailWord_8119767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119767).length < 2 ^ (prefixWord ++ tailWord_8119767).sum := by decide
  have hdescent : baseEnd_8119767 < baseStart_8119767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119781 : List Nat := [1, 3, 1, 5, 1, 1, 2, 3, 1, 1, 4]
def baseStart_8119781 : Nat := 118140960795 + 8119781 * 2 ^ 59
def prefixEnd_8119781 : Nat := 4983230072969 + 3 ^ 40 * 8119781 * 2
def baseEnd_8119781 : Nat := 4169350462245001053195313

theorem tailTrace_8119781 : CollatzResearch.WordTrace tailWord_8119781 prefixEnd_8119781 4169350462245001053195313 := by
  unfold tailWord_8119781
  simp only [CollatzResearch.WordTrace]
  refine ⟨296152742996427660035247197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197435161997618440023498131 296152742996427660035247197)
  ·
    refine ⟨111057278623660372513217699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296152742996427660035247197 111057278623660372513217699)
    ·
      refine ⟨166585917935490558769826549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111057278623660372513217699 166585917935490558769826549)
      ·
        refine ⟨15617429806452239884671239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166585917935490558769826549 15617429806452239884671239)
        ·
          refine ⟨23426144709678359827006859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15617429806452239884671239 23426144709678359827006859)
          ·
            refine ⟨35139217064517539740510289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23426144709678359827006859 35139217064517539740510289)
            ·
              refine ⟨26354412798388154805382717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35139217064517539740510289 26354412798388154805382717)
              ·
                refine ⟨9882904799395558052018519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26354412798388154805382717 9882904799395558052018519)
                ·
                  refine ⟨14824357199093337078027779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9882904799395558052018519 14824357199093337078027779)
                  ·
                    refine ⟨22236535798640005617041669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14824357199093337078027779 22236535798640005617041669)
                    ·
                      refine ⟨4169350462245001053195313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22236535798640005617041669 4169350462245001053195313)
                      ·
                        rfl

theorem cell23_8119781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_8119781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119781 prefixEnd_8119781 := by exact prefixLift 8119781
  have htrace : WordTrace (prefixWord ++ tailWord_8119781) baseStart_8119781 baseEnd_8119781 := by
    simpa [prefixWord, tailWord_8119781, baseEnd_8119781] using wordTrace_append hprefix tailTrace_8119781
  have hstable : (prefixWord ++ tailWord_8119781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119781).length < 2 ^ (prefixWord ++ tailWord_8119781).sum := by decide
  have hdescent : baseEnd_8119781 < baseStart_8119781 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119784 : List Nat := [2, 1, 4, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_8119784 : Nat := 118140960795 + 8119784 * 2 ^ 59
def prefixEnd_8119784 : Nat := 4983230072969 + 3 ^ 40 * 8119784 * 2
def baseEnd_8119784 : Nat := 4169352002686964541457799

theorem tailTrace_8119784 : CollatzResearch.WordTrace tailWord_8119784 prefixEnd_8119784 4169352002686964541457799 := by
  unfold tailWord_8119784
  simp only [CollatzResearch.WordTrace]
  refine ⟨148076426207708395773803203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197435234943611194365070937 148076426207708395773803203)
  ·
    refine ⟨222114639311562593660704805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148076426207708395773803203 222114639311562593660704805)
    ·
      refine ⟨41646494870917986311382151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222114639311562593660704805 41646494870917986311382151)
      ·
        refine ⟨62469742306376979467073227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41646494870917986311382151 62469742306376979467073227)
        ·
          refine ⟨93704613459565469200609841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62469742306376979467073227 93704613459565469200609841)
          ·
            refine ⟨70278460094674101900457381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93704613459565469200609841 70278460094674101900457381)
            ·
              refine ⟨13177211267751394106335759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70278460094674101900457381 13177211267751394106335759)
              ·
                refine ⟨19765816901627091159503639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13177211267751394106335759 19765816901627091159503639)
                ·
                  refine ⟨29648725352440636739255459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19765816901627091159503639 29648725352440636739255459)
                  ·
                    refine ⟨44473088028660955108883189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29648725352440636739255459 44473088028660955108883189)
                    ·
                      refine ⟨4169352002686964541457799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44473088028660955108883189 4169352002686964541457799)
                      ·
                        rfl

theorem cell23_8119784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_8119784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119784 prefixEnd_8119784 := by exact prefixLift 8119784
  have htrace : WordTrace (prefixWord ++ tailWord_8119784) baseStart_8119784 baseEnd_8119784 := by
    simpa [prefixWord, tailWord_8119784, baseEnd_8119784] using wordTrace_append hprefix tailTrace_8119784
  have hstable : (prefixWord ++ tailWord_8119784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119784).length < 2 ^ (prefixWord ++ tailWord_8119784).sum := by decide
  have hdescent : baseEnd_8119784 < baseStart_8119784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119794 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_8119794 : Nat := 118140960795 + 8119794 * 2 ^ 59
def prefixEnd_8119794 : Nat := 4983230072969 + 3 ^ 40 * 8119794 * 2
def baseEnd_8119794 : Nat := 4169357137493509502332753

theorem tailTrace_8119794 : CollatzResearch.WordTrace tailWord_8119794 prefixEnd_8119794 4169357137493509502332753 := by
  unfold tailWord_8119794
  simp only [CollatzResearch.WordTrace]
  refine ⟨74038304286345140813867609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197435478096920375503646957 74038304286345140813867609)
  ·
    refine ⟨55528728214758855610400707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74038304286345140813867609 55528728214758855610400707)
    ·
      refine ⟨83293092322138283415601061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55528728214758855610400707 83293092322138283415601061)
      ·
        refine ⟨15617454810400928140425199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83293092322138283415601061 15617454810400928140425199)
        ·
          refine ⟨23426182215601392210637799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15617454810400928140425199 23426182215601392210637799)
          ·
            refine ⟨35139273323402088315956699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23426182215601392210637799 35139273323402088315956699)
            ·
              refine ⟨52708909985103132473935049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35139273323402088315956699 52708909985103132473935049)
              ·
                refine ⟨39531682488827349355451287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52708909985103132473935049 39531682488827349355451287)
                ·
                  refine ⟨59297523733241024033176931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39531682488827349355451287 59297523733241024033176931)
                  ·
                    refine ⟨88946285599861536049765397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59297523733241024033176931 88946285599861536049765397)
                    ·
                      refine ⟨4169357137493509502332753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88946285599861536049765397 4169357137493509502332753)
                      ·
                        rfl

theorem cell23_8119794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_8119794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119794 prefixEnd_8119794 := by exact prefixLift 8119794
  have htrace : WordTrace (prefixWord ++ tailWord_8119794) baseStart_8119794 baseEnd_8119794 := by
    simpa [prefixWord, tailWord_8119794, baseEnd_8119794] using wordTrace_append hprefix tailTrace_8119794
  have hstable : (prefixWord ++ tailWord_8119794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119794).length < 2 ^ (prefixWord ++ tailWord_8119794).sum := by decide
  have hdescent : baseEnd_8119794 < baseStart_8119794 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119818 : List Nat := [3, 1, 2, 2, 2, 4, 1, 2, 1, 2, 3]
def baseStart_8119818 : Nat := 118140960795 + 8119818 * 2 ^ 59
def prefixEnd_8119818 : Nat := 4983230072969 + 3 ^ 40 * 8119818 * 2
def baseEnd_8119818 : Nat := 4169369461029217408432643

theorem tailTrace_8119818 : CollatzResearch.WordTrace tailWord_8119818 prefixEnd_8119818 4169369461029217408432643 := by
  unfold tailWord_8119818
  simp only [CollatzResearch.WordTrace]
  refine ⟨74038523124323403838586027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197436061664862410236229405 74038523124323403838586027)
  ·
    refine ⟨111057784686485105757879041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74038523124323403838586027 111057784686485105757879041)
    ·
      refine ⟨83293338514863829318409281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111057784686485105757879041 83293338514863829318409281)
      ·
        refine ⟨62470003886147871988806961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83293338514863829318409281 62470003886147871988806961)
        ·
          refine ⟨46852502914610903991605221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62470003886147871988806961 46852502914610903991605221)
          ·
            refine ⟨8784844296489544498425979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46852502914610903991605221 8784844296489544498425979)
            ·
              refine ⟨13177266444734316747638969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8784844296489544498425979 13177266444734316747638969)
              ·
                refine ⟨9882949833550737560729227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13177266444734316747638969 9882949833550737560729227)
                ·
                  refine ⟨14824424750326106341093841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9882949833550737560729227 14824424750326106341093841)
                  ·
                    refine ⟨11118318562744579755820381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14824424750326106341093841 11118318562744579755820381)
                    ·
                      refine ⟨4169369461029217408432643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11118318562744579755820381 4169369461029217408432643)
                      ·
                        rfl

theorem cell23_8119818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_8119818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119818 prefixEnd_8119818 := by exact prefixLift 8119818
  have htrace : WordTrace (prefixWord ++ tailWord_8119818) baseStart_8119818 baseEnd_8119818 := by
    simpa [prefixWord, tailWord_8119818, baseEnd_8119818] using wordTrace_append hprefix tailTrace_8119818
  have hstable : (prefixWord ++ tailWord_8119818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119818).length < 2 ^ (prefixWord ++ tailWord_8119818).sum := by decide
  have hdescent : baseEnd_8119818 < baseStart_8119818 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119828 : List Nat := [2, 4, 3, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_8119828 : Nat := 118140960795 + 8119828 * 2 ^ 59
def prefixEnd_8119828 : Nat := 4983230072969 + 3 ^ 40 * 8119828 * 2
def baseEnd_8119828 : Nat := 4169374595835762369307597

theorem tailTrace_8119828 : CollatzResearch.WordTrace tailWord_8119828 prefixEnd_8119828 4169374595835762369307597 := by
  unfold tailWord_8119828
  simp only [CollatzResearch.WordTrace]
  refine ⟨148077228613628693531104069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197436304818171591374805425 148077228613628693531104069)
  ·
    refine ⟨27764480365055380037082013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148077228613628693531104069 27764480365055380037082013)
    ·
      refine ⟨10411680136895767513905755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27764480365055380037082013 10411680136895767513905755)
      ·
        refine ⟨15617520205343651270858633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10411680136895767513905755 15617520205343651270858633)
        ·
          refine ⟨11713140154007738453143975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15617520205343651270858633 11713140154007738453143975)
          ·
            refine ⟨17569710231011607679715963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11713140154007738453143975 17569710231011607679715963)
            ·
              refine ⟨26354565346517411519573945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17569710231011607679715963 26354565346517411519573945)
              ·
                refine ⟨19765924009888058639680459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26354565346517411519573945 19765924009888058639680459)
                ·
                  refine ⟨29648886014832087959520689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19765924009888058639680459 29648886014832087959520689)
                  ·
                    refine ⟨22236664511124065969640517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29648886014832087959520689 22236664511124065969640517)
                    ·
                      refine ⟨4169374595835762369307597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22236664511124065969640517 4169374595835762369307597)
                      ·
                        rfl

theorem cell23_8119828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_8119828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119828 prefixEnd_8119828 := by exact prefixLift 8119828
  have htrace : WordTrace (prefixWord ++ tailWord_8119828) baseStart_8119828 baseEnd_8119828 := by
    simpa [prefixWord, tailWord_8119828, baseEnd_8119828] using wordTrace_append hprefix tailTrace_8119828
  have hstable : (prefixWord ++ tailWord_8119828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119828).length < 2 ^ (prefixWord ++ tailWord_8119828).sum := by decide
  have hdescent : baseEnd_8119828 < baseStart_8119828 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119838 : List Nat := [4, 3, 3, 1, 1, 11]
def baseStart_8119838 : Nat := 118140960795 + 8119838 * 2 ^ 59
def prefixEnd_8119838 : Nat := 4983230072969 + 3 ^ 40 * 8119838 * 2
def baseEnd_8119838 : Nat := 17157941278363404650957

theorem tailTrace_8119838 : CollatzResearch.WordTrace tailWord_8119838 prefixEnd_8119838 17157941278363404650957 := by
  unfold tailWord_8119838
  simp only [CollatzResearch.WordTrace]
  refine ⟨37019352744652644846259021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197436547971480772513381445 37019352744652644846259021)
  ·
    refine ⟨13882257279244741817347133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37019352744652644846259021 13882257279244741817347133)
    ·
      refine ⟨5205846479716778181505175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13882257279244741817347133 5205846479716778181505175)
      ·
        refine ⟨7808769719575167272257763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5205846479716778181505175 7808769719575167272257763)
        ·
          refine ⟨11713154579362750908386645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7808769719575167272257763 11713154579362750908386645)
          ·
            refine ⟨17157941278363404650957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11713154579362750908386645 17157941278363404650957)
            ·
              rfl

theorem cell23_8119838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 11].length) (baseStart_8119838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119838 prefixEnd_8119838 := by exact prefixLift 8119838
  have htrace : WordTrace (prefixWord ++ tailWord_8119838) baseStart_8119838 baseEnd_8119838 := by
    simpa [prefixWord, tailWord_8119838, baseEnd_8119838] using wordTrace_append hprefix tailTrace_8119838
  have hstable : (prefixWord ++ tailWord_8119838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119838).length < 2 ^ (prefixWord ++ tailWord_8119838).sum := by decide
  have hdescent : baseEnd_8119838 < baseStart_8119838 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119864 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 2, 6]
def baseStart_8119864 : Nat := 118140960795 + 8119864 * 2 ^ 59
def prefixEnd_8119864 : Nat := 4983230072969 + 3 ^ 40 * 8119864 * 2
def baseEnd_8119864 : Nat := 1389797693713108076152477

theorem tailTrace_8119864 : CollatzResearch.WordTrace tailWord_8119864 prefixEnd_8119864 1389797693713108076152477 := by
  unfold tailWord_8119864
  simp only [CollatzResearch.WordTrace]
  refine ⟨148077885127563482605259323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197437180170084643473679097 148077885127563482605259323)
  ·
    refine ⟨222116827691345223907888985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148077885127563482605259323 222116827691345223907888985)
    ·
      refine ⟨166587620768508917930916739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222116827691345223907888985 166587620768508917930916739)
      ·
        refine ⟨249881431152763376896375109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166587620768508917930916739 249881431152763376896375109)
        ·
          refine ⟨46852768341143133168070333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249881431152763376896375109 46852768341143133168070333)
          ·
            refine ⟨17569788127928674938026375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46852768341143133168070333 17569788127928674938026375)
            ·
              refine ⟨26354682191893012407039563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17569788127928674938026375 26354682191893012407039563)
              ·
                refine ⟨39532023287839518610559345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26354682191893012407039563 39532023287839518610559345)
                ·
                  refine ⟨29649017465879638957919509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39532023287839518610559345 29649017465879638957919509)
                  ·
                    refine ⟨1389797693713108076152477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29649017465879638957919509 1389797693713108076152477)
                    ·
                      rfl

theorem cell23_8119864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_8119864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119864 prefixEnd_8119864 := by exact prefixLift 8119864
  have htrace : WordTrace (prefixWord ++ tailWord_8119864) baseStart_8119864 baseEnd_8119864 := by
    simpa [prefixWord, tailWord_8119864, baseEnd_8119864] using wordTrace_append hprefix tailTrace_8119864
  have hstable : (prefixWord ++ tailWord_8119864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119864).length < 2 ^ (prefixWord ++ tailWord_8119864).sum := by decide
  have hdescent : baseEnd_8119864 < baseStart_8119864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119871 : List Nat := [1, 1, 2, 2, 3, 3, 1, 3, 1, 4, 2]
def baseStart_8119871 : Nat := 118140960795 + 8119871 * 2 ^ 59
def prefixEnd_8119871 : Nat := 4983230072969 + 3 ^ 40 * 8119871 * 2
def baseEnd_8119871 : Nat := 4169396675503905701069899

theorem tailTrace_8119871 : CollatzResearch.WordTrace tailWord_8119871 prefixEnd_8119871 4169396675503905701069899 := by
  unfold tailWord_8119871
  simp only [CollatzResearch.WordTrace]
  refine ⟨296156025566101605406023467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197437350377401070270682311 296156025566101605406023467)
  ·
    refine ⟨444234038349152408109035201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296156025566101605406023467 444234038349152408109035201)
    ·
      refine ⟨333175528761864306081776401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444234038349152408109035201 333175528761864306081776401)
      ·
        refine ⟨249881646571398229561332301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333175528761864306081776401 249881646571398229561332301)
        ·
          refine ⟨93705617464274336085499613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249881646571398229561332301 93705617464274336085499613)
          ·
            refine ⟨35139606549102876032062355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93705617464274336085499613 35139606549102876032062355)
            ·
              refine ⟨52709409823654314048093533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35139606549102876032062355 52709409823654314048093533)
              ·
                refine ⟨19766028683870367768035075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52709409823654314048093533 19766028683870367768035075)
                ·
                  refine ⟨29649043025805551652052613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19766028683870367768035075 29649043025805551652052613)
                  ·
                    refine ⟨5559195567338540934759865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29649043025805551652052613 5559195567338540934759865)
                    ·
                      refine ⟨4169396675503905701069899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5559195567338540934759865 4169396675503905701069899)
                      ·
                        rfl

theorem cell23_8119871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 4, 2].length) (baseStart_8119871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119871 prefixEnd_8119871 := by exact prefixLift 8119871
  have htrace : WordTrace (prefixWord ++ tailWord_8119871) baseStart_8119871 baseEnd_8119871 := by
    simpa [prefixWord, tailWord_8119871, baseEnd_8119871] using wordTrace_append hprefix tailTrace_8119871
  have hstable : (prefixWord ++ tailWord_8119871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119871).length < 2 ^ (prefixWord ++ tailWord_8119871).sum := by decide
  have hdescent : baseEnd_8119871 < baseStart_8119871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119887 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 7]
def baseStart_8119887 : Nat := 118140960795 + 8119887 * 2 ^ 59
def prefixEnd_8119887 : Nat := 4983230072969 + 3 ^ 40 * 8119887 * 2
def baseEnd_8119887 : Nat := 4169404891194377638469825

theorem tailTrace_8119887 : CollatzResearch.WordTrace tailWord_8119887 prefixEnd_8119887 4169404891194377638469825 := by
  unfold tailWord_8119887
  simp only [CollatzResearch.WordTrace]
  refine ⟨296156609134043640138605915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197437739422695760092403943 296156609134043640138605915)
  ·
    refine ⟨444234913701065460207908873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296156609134043640138605915 444234913701065460207908873)
    ·
      refine ⟨333176185275799095155931655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444234913701065460207908873 333176185275799095155931655)
      ·
        refine ⟨499764277913698642733897483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333176185275799095155931655 499764277913698642733897483)
        ·
          refine ⟨749646416870547964100846225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499764277913698642733897483 749646416870547964100846225)
          ·
            refine ⟨562234812652910973075634669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 749646416870547964100846225 562234812652910973075634669)
            ·
              refine ⟨210838054744841614903363001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 562234812652910973075634669 210838054744841614903363001)
              ·
                refine ⟨158128541058631211177522251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210838054744841614903363001 158128541058631211177522251)
                ·
                  refine ⟨237192811587946816766283377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158128541058631211177522251 237192811587946816766283377)
                  ·
                    refine ⟨177894608690960112574712533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 237192811587946816766283377 177894608690960112574712533)
                    ·
                      refine ⟨4169404891194377638469825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177894608690960112574712533 4169404891194377638469825)
                      ·
                        rfl

theorem cell23_8119887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_8119887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119887 prefixEnd_8119887 := by exact prefixLift 8119887
  have htrace : WordTrace (prefixWord ++ tailWord_8119887) baseStart_8119887 baseEnd_8119887 := by
    simpa [prefixWord, tailWord_8119887, baseEnd_8119887] using wordTrace_append hprefix tailTrace_8119887
  have hstable : (prefixWord ++ tailWord_8119887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119887).length < 2 ^ (prefixWord ++ tailWord_8119887).sum := by decide
  have hdescent : baseEnd_8119887 < baseStart_8119887 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119911 : List Nat := [1, 1, 5, 1, 1, 1, 4, 4, 5]
def baseStart_8119911 : Nat := 118140960795 + 8119911 * 2 ^ 59
def prefixEnd_8119911 : Nat := 4983230072969 + 3 ^ 40 * 8119911 * 2
def baseEnd_8119911 : Nat := 463268579414453949396635

theorem tailTrace_8119911 : CollatzResearch.WordTrace tailWord_8119911 prefixEnd_8119911 463268579414453949396635 := by
  unfold tailWord_8119911
  simp only [CollatzResearch.WordTrace]
  refine ⟨296157484485956692237479587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197438322990637794824986391 296157484485956692237479587)
  ·
    refine ⟨444236226728935038356219381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296157484485956692237479587 444236226728935038356219381)
    ·
      refine ⟨41647146255837659845895567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 444236226728935038356219381 41647146255837659845895567)
      ·
        refine ⟨62470719383756489768843351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41647146255837659845895567 62470719383756489768843351)
        ·
          refine ⟨93706079075634734653265027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62470719383756489768843351 93706079075634734653265027)
          ·
            refine ⟨140559118613452101979897541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93706079075634734653265027 140559118613452101979897541)
            ·
              refine ⟨26354834740022269121230789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140559118613452101979897541 26354834740022269121230789)
              ·
                refine ⟨4941531513754175460230773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26354834740022269121230789 4941531513754175460230773)
                ·
                  refine ⟨463268579414453949396635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4941531513754175460230773 463268579414453949396635)
                  ·
                    rfl

theorem cell23_8119911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 5].length) (baseStart_8119911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119911 prefixEnd_8119911 := by exact prefixLift 8119911
  have htrace : WordTrace (prefixWord ++ tailWord_8119911) baseStart_8119911 baseEnd_8119911 := by
    simpa [prefixWord, tailWord_8119911, baseEnd_8119911] using wordTrace_append hprefix tailTrace_8119911
  have hstable : (prefixWord ++ tailWord_8119911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119911).length < 2 ^ (prefixWord ++ tailWord_8119911).sum := by decide
  have hdescent : baseEnd_8119911 < baseStart_8119911 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119922 : List Nat := [3, 2, 1, 2, 3, 2, 3, 1, 2, 2, 2]
def baseStart_8119922 : Nat := 118140960795 + 8119922 * 2 ^ 59
def prefixEnd_8119922 : Nat := 4983230072969 + 3 ^ 40 * 8119922 * 2
def baseEnd_8119922 : Nat := 4169422863017285001532165

theorem tailTrace_8119922 : CollatzResearch.WordTrace tailWord_8119922 prefixEnd_8119922 4169422863017285001532165 := by
  unfold tailWord_8119922
  simp only [CollatzResearch.WordTrace]
  refine ⟨74039471422229210279032505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197438590459277894077420013 74039471422229210279032505)
  ·
    refine ⟨55529603566671907709274379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74039471422229210279032505 55529603566671907709274379)
    ·
      refine ⟨83294405350007861563911569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55529603566671907709274379 83294405350007861563911569)
      ·
        refine ⟨62470804012505896172933677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83294405350007861563911569 62470804012505896172933677)
        ·
          refine ⟨23426551504689711064850129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62470804012505896172933677 23426551504689711064850129)
          ·
            refine ⟨17569913628517283298637597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23426551504689711064850129 17569913628517283298637597)
            ·
              refine ⟨6588717610693981236989099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17569913628517283298637597 6588717610693981236989099)
              ·
                refine ⟨9883076416040971855483649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6588717610693981236989099 9883076416040971855483649)
                ·
                  refine ⟨7412307312030728891612737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9883076416040971855483649 7412307312030728891612737)
                  ·
                    refine ⟨5559230484023046668709553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7412307312030728891612737 5559230484023046668709553)
                    ·
                      refine ⟨4169422863017285001532165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5559230484023046668709553 4169422863017285001532165)
                      ·
                        rfl

theorem cell23_8119922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_8119922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119922 prefixEnd_8119922 := by exact prefixLift 8119922
  have htrace : WordTrace (prefixWord ++ tailWord_8119922) baseStart_8119922 baseEnd_8119922 := by
    simpa [prefixWord, tailWord_8119922, baseEnd_8119922] using wordTrace_append hprefix tailTrace_8119922
  have hstable : (prefixWord ++ tailWord_8119922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119922).length < 2 ^ (prefixWord ++ tailWord_8119922).sum := by decide
  have hdescent : baseEnd_8119922 < baseStart_8119922 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
