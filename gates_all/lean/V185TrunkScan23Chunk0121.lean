import V185TrunkScan23Chunk0120

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_716266 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 4, 2, 2]
def baseStart_716266 : Nat := 118140960795 + 716266 * 2 ^ 59
def prefixEnd_716266 : Nat := 4983230072969 + 3 ^ 40 * 716266 * 2
def baseEnd_716266 : Nat := 367788734473399839680959

theorem tailTrace_716266 : CollatzResearch.WordTrace tailWord_716266 prefixEnd_716266 367788734473399839680959 := by
  unfold tailWord_716266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6531091805774521334710163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17416244815398723559227101 6531091805774521334710163)
  ·
    refine ⟨9796637708661782002065245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6531091805774521334710163 9796637708661782002065245)
    ·
      refine ⟨3673739140748168250774467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9796637708661782002065245 3673739140748168250774467)
      ·
        refine ⟨5510608711122252376161701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3673739140748168250774467 5510608711122252376161701)
        ·
          refine ⟨1033239133335422320530319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5510608711122252376161701 1033239133335422320530319)
          ·
            refine ⟨1549858700003133480795479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033239133335422320530319 1549858700003133480795479)
            ·
              refine ⟨2324788050004700221193219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1549858700003133480795479 2324788050004700221193219)
              ·
                refine ⟨3487182075007050331789829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2324788050004700221193219 3487182075007050331789829)
                ·
                  refine ⟨653846639063821937210593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3487182075007050331789829 653846639063821937210593)
                  ·
                    refine ⟨490384979297866452907945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 653846639063821937210593 490384979297866452907945)
                    ·
                      refine ⟨367788734473399839680959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 490384979297866452907945 367788734473399839680959)
                      ·
                        rfl

theorem cell23_716266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_716266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716266 prefixEnd_716266 := by exact prefixLift 716266
  have htrace : WordTrace (prefixWord ++ tailWord_716266) baseStart_716266 baseEnd_716266 := by
    simpa [prefixWord, tailWord_716266, baseEnd_716266] using wordTrace_append hprefix tailTrace_716266
  have hstable : (prefixWord ++ tailWord_716266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716266).length < 2 ^ (prefixWord ++ tailWord_716266).sum := by decide
  have hdescent : baseEnd_716266 < baseStart_716266 := by decide
  rcases family_descends (prefixWord ++ tailWord_716266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716272 : List Nat := [2, 1, 1, 1, 3, 4, 2, 4, 5]
def baseStart_716272 : Nat := 118140960795 + 716272 * 2 ^ 59
def prefixEnd_716272 : Nat := 4983230072969 + 3 ^ 40 * 716272 * 2
def baseEnd_716272 : Nat := 40865757261925201800659

theorem tailTrace_716272 : CollatzResearch.WordTrace tailWord_716272 prefixEnd_716272 40865757261925201800659 := by
  unfold tailWord_716272
  simp only [CollatzResearch.WordTrace]
  refine ⟨13062293030538174181779535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17416390707384232242372713 13062293030538174181779535)
  ·
    refine ⟨19593439545807261272669303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13062293030538174181779535 19593439545807261272669303)
    ·
      refine ⟨29390159318710891909003955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19593439545807261272669303 29390159318710891909003955)
      ·
        refine ⟨44085238978066337863505933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29390159318710891909003955 44085238978066337863505933)
        ·
          refine ⟨16531964616774876698814725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44085238978066337863505933 16531964616774876698814725)
          ·
            refine ⟨3099743365645289381027761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16531964616774876698814725 3099743365645289381027761)
            ·
              refine ⟨2324807524233967035770821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3099743365645289381027761 2324807524233967035770821)
              ·
                refine ⟨435901410793868819207029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2324807524233967035770821 435901410793868819207029)
                ·
                  refine ⟨40865757261925201800659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 435901410793868819207029 40865757261925201800659)
                  ·
                    rfl

theorem cell23_716272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 5].length) (baseStart_716272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716272 prefixEnd_716272 := by exact prefixLift 716272
  have htrace : WordTrace (prefixWord ++ tailWord_716272) baseStart_716272 baseEnd_716272 := by
    simpa [prefixWord, tailWord_716272, baseEnd_716272] using wordTrace_append hprefix tailTrace_716272
  have hstable : (prefixWord ++ tailWord_716272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716272).length < 2 ^ (prefixWord ++ tailWord_716272).sum := by decide
  have hdescent : baseEnd_716272 < baseStart_716272 := by decide
  rcases family_descends (prefixWord ++ tailWord_716272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716285 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 1, 7]
def baseStart_716285 : Nat := 118140960795 + 716285 * 2 ^ 59
def prefixEnd_716285 : Nat := 4983230072969 + 3 ^ 40 * 716285 * 2
def baseEnd_716285 : Nat := 122599496868611755114457

theorem tailTrace_716285 : CollatzResearch.WordTrace tailWord_716285 prefixEnd_716285 122599496868611755114457 := by
  unfold tailWord_716285
  simp only [CollatzResearch.WordTrace]
  refine ⟨26125060210029251583782309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17416706806686167722521539 26125060210029251583782309)
  ·
    refine ⟨4898448789380484671959183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26125060210029251583782309 4898448789380484671959183)
    ·
      refine ⟨7347673184070727007938775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4898448789380484671959183 7347673184070727007938775)
      ·
        refine ⟨11021509776106090511908163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7347673184070727007938775 11021509776106090511908163)
        ·
          refine ⟨16532264664159135767862245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11021509776106090511908163 16532264664159135767862245)
          ·
            refine ⟨3099799624529837956474171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16532264664159135767862245 3099799624529837956474171)
            ·
              refine ⟨4649699436794756934711257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3099799624529837956474171 4649699436794756934711257)
              ·
                refine ⟨3487274577596067701033443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4649699436794756934711257 3487274577596067701033443)
                ·
                  refine ⟨5230911866394101551550165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3487274577596067701033443 5230911866394101551550165)
                  ·
                    refine ⟨122599496868611755114457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5230911866394101551550165 122599496868611755114457)
                    ·
                      rfl

theorem cell23_716285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_716285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716285 prefixEnd_716285 := by exact prefixLift 716285
  have htrace : WordTrace (prefixWord ++ tailWord_716285) baseStart_716285 baseEnd_716285 := by
    simpa [prefixWord, tailWord_716285, baseEnd_716285] using wordTrace_append hprefix tailTrace_716285
  have hstable : (prefixWord ++ tailWord_716285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716285).length < 2 ^ (prefixWord ++ tailWord_716285).sum := by decide
  have hdescent : baseEnd_716285 < baseStart_716285 := by decide
  rcases family_descends (prefixWord ++ tailWord_716285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716305 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 4]
def baseStart_716305 : Nat := 118140960795 + 716305 * 2 ^ 59
def prefixEnd_716305 : Nat := 4983230072969 + 3 ^ 40 * 716305 * 2
def baseEnd_716305 : Nat := 367808760218925187093279

theorem tailTrace_716305 : CollatzResearch.WordTrace tailWord_716305 prefixEnd_716305 367808760218925187093279 := by
  unfold tailWord_716305
  simp only [CollatzResearch.WordTrace]
  refine ⟨26125789669956794999510369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17417193113304529999673579 26125789669956794999510369)
  ·
    refine ⟨19594342252467596249632777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26125789669956794999510369 19594342252467596249632777)
    ·
      refine ⟨14695756689350697187224583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19594342252467596249632777 14695756689350697187224583)
      ·
        refine ⟨22043635034026045780836875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14695756689350697187224583 22043635034026045780836875)
        ·
          refine ⟨33065452551039068671255313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22043635034026045780836875 33065452551039068671255313)
          ·
            refine ⟨24799089413279301503441485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33065452551039068671255313 24799089413279301503441485)
            ·
              refine ⟨9299658529979738063790557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24799089413279301503441485 9299658529979738063790557)
              ·
                refine ⟨3487371948742401773921459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9299658529979738063790557 3487371948742401773921459)
                ·
                  refine ⟨5231057923113602660882189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3487371948742401773921459 5231057923113602660882189)
                  ·
                    refine ⟨1961646721167600997830821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5231057923113602660882189 1961646721167600997830821)
                    ·
                      refine ⟨367808760218925187093279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1961646721167600997830821 367808760218925187093279)
                      ·
                        rfl

theorem cell23_716305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_716305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716305 prefixEnd_716305 := by exact prefixLift 716305
  have htrace : WordTrace (prefixWord ++ tailWord_716305) baseStart_716305 baseEnd_716305 := by
    simpa [prefixWord, tailWord_716305, baseEnd_716305] using wordTrace_append hprefix tailTrace_716305
  have hstable : (prefixWord ++ tailWord_716305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716305).length < 2 ^ (prefixWord ++ tailWord_716305).sum := by decide
  have hdescent : baseEnd_716305 < baseStart_716305 := by decide
  rcases family_descends (prefixWord ++ tailWord_716305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716322 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_716322 : Nat := 118140960795 + 716322 * 2 ^ 59
def prefixEnd_716322 : Nat := 4983230072969 + 3 ^ 40 * 716322 * 2
def baseEnd_716322 : Nat := 367817489390051620580701

theorem tailTrace_716322 : CollatzResearch.WordTrace tailWord_716322 prefixEnd_716322 367817489390051620580701 := by
  unfold tailWord_716322
  simp only [CollatzResearch.WordTrace]
  refine ⟨6531602427723801725719805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17417606473930137935252813 6531602427723801725719805)
  ·
    refine ⟨2449350910396425647144927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6531602427723801725719805 2449350910396425647144927)
    ·
      refine ⟨3674026365594638470717391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2449350910396425647144927 3674026365594638470717391)
      ·
        refine ⟨5511039548391957706076087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3674026365594638470717391 5511039548391957706076087)
        ·
          refine ⟨8266559322587936559114131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5511039548391957706076087 8266559322587936559114131)
          ·
            refine ⟨12399838983881904838671197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8266559322587936559114131 12399838983881904838671197)
            ·
              refine ⟨4649939618955714314501699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12399838983881904838671197 4649939618955714314501699)
              ·
                refine ⟨6974909428433571471752549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4649939618955714314501699 6974909428433571471752549)
                ·
                  refine ⟨1307795517831294650953603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6974909428433571471752549 1307795517831294650953603)
                  ·
                    refine ⟨1961693276746941976430405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1307795517831294650953603 1961693276746941976430405)
                    ·
                      refine ⟨367817489390051620580701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1961693276746941976430405 367817489390051620580701)
                      ·
                        rfl

theorem cell23_716322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_716322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716322 prefixEnd_716322 := by exact prefixLift 716322
  have htrace : WordTrace (prefixWord ++ tailWord_716322) baseStart_716322 baseEnd_716322 := by
    simpa [prefixWord, tailWord_716322, baseEnd_716322] using wordTrace_append hprefix tailTrace_716322
  have hstable : (prefixWord ++ tailWord_716322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716322).length < 2 ^ (prefixWord ++ tailWord_716322).sum := by decide
  have hdescent : baseEnd_716322 < baseStart_716322 := by decide
  rcases family_descends (prefixWord ++ tailWord_716322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716406 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_716406 : Nat := 118140960795 + 716406 * 2 ^ 59
def prefixEnd_716406 : Nat := 4983230072969 + 3 ^ 40 * 716406 * 2
def baseEnd_716406 : Nat := 367860621765029291930315

theorem tailTrace_716406 : CollatzResearch.WordTrace tailWord_716406 prefixEnd_716406 367860621765029291930315 := by
  unfold tailWord_716406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1633092090161930578058567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17419648961727259499291381 1633092090161930578058567)
  ·
    refine ⟨2449638135242895867087851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1633092090161930578058567 2449638135242895867087851)
    ·
      refine ⟨3674457202864343800631777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2449638135242895867087851 3674457202864343800631777)
      ·
        refine ⟨2755842902148257850473833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3674457202864343800631777 2755842902148257850473833)
        ·
          refine ⟨2066882176611193387855375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2755842902148257850473833 2066882176611193387855375)
          ·
            refine ⟨3100323264916790081783063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2066882176611193387855375 3100323264916790081783063)
            ·
              refine ⟨4650484897375185122674595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3100323264916790081783063 4650484897375185122674595)
              ·
                refine ⟨6975727346062777684011893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4650484897375185122674595 6975727346062777684011893)
                ·
                  refine ⟨653974438693385407876115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6975727346062777684011893 653974438693385407876115)
                  ·
                    refine ⟨980961658040078111814173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 653974438693385407876115 980961658040078111814173)
                    ·
                      refine ⟨367860621765029291930315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 980961658040078111814173 367860621765029291930315)
                      ·
                        rfl

theorem cell23_716406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_716406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716406 prefixEnd_716406 := by exact prefixLift 716406
  have htrace : WordTrace (prefixWord ++ tailWord_716406) baseStart_716406 baseEnd_716406 := by
    simpa [prefixWord, tailWord_716406, baseEnd_716406] using wordTrace_append hprefix tailTrace_716406
  have hstable : (prefixWord ++ tailWord_716406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716406).length < 2 ^ (prefixWord ++ tailWord_716406).sum := by decide
  have hdescent : baseEnd_716406 < baseStart_716406 := by decide
  rcases family_descends (prefixWord ++ tailWord_716406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716423 : List Nat := [1, 1, 4, 2, 1, 4, 2, 3, 1, 1, 3]
def baseStart_716423 : Nat := 118140960795 + 716423 * 2 ^ 59
def prefixEnd_716423 : Nat := 4983230072969 + 3 ^ 40 * 716423 * 2
def baseEnd_716423 : Nat := 367869350936155725417737

theorem tailTrace_716423 : CollatzResearch.WordTrace tailWord_716423 prefixEnd_716423 367869350936155725417737 := by
  unfold tailWord_716423
  simp only [CollatzResearch.WordTrace]
  refine ⟨26130093483529301152305923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17420062322352867434870615 26130093483529301152305923)
  ·
    refine ⟨39195140225293951728458885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26130093483529301152305923 39195140225293951728458885)
    ·
      refine ⟨7349088792242615949086041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39195140225293951728458885 7349088792242615949086041)
      ·
        refine ⟨5511816594181961961814531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7349088792242615949086041 5511816594181961961814531)
        ·
          refine ⟨8267724891272942942721797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5511816594181961961814531 8267724891272942942721797)
          ·
            refine ⟨1550198417113676801760337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8267724891272942942721797 1550198417113676801760337)
            ·
              refine ⟨1162648812835257601320253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1550198417113676801760337 1162648812835257601320253)
              ·
                refine ⟨435993304813221600495095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1162648812835257601320253 435993304813221600495095)
                ·
                  refine ⟨653989957219832400742643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435993304813221600495095 653989957219832400742643)
                  ·
                    refine ⟨980984935829748601113965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 653989957219832400742643 980984935829748601113965)
                    ·
                      refine ⟨367869350936155725417737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 980984935829748601113965 367869350936155725417737)
                      ·
                        rfl

theorem cell23_716423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_716423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716423 prefixEnd_716423 := by exact prefixLift 716423
  have htrace : WordTrace (prefixWord ++ tailWord_716423) baseStart_716423 baseEnd_716423 := by
    simpa [prefixWord, tailWord_716423, baseEnd_716423] using wordTrace_append hprefix tailTrace_716423
  have hstable : (prefixWord ++ tailWord_716423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716423).length < 2 ^ (prefixWord ++ tailWord_716423).sum := by decide
  have hdescent : baseEnd_716423 < baseStart_716423 := by decide
  rcases family_descends (prefixWord ++ tailWord_716423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716426 : List Nat := [3, 1, 2, 3, 2, 1, 4, 1, 1, 5]
def baseStart_716426 : Nat := 118140960795 + 716426 * 2 ^ 59
def prefixEnd_716426 : Nat := 4983230072969 + 3 ^ 40 * 716426 * 2
def baseEnd_716426 : Nat := 122623630459373071226741

theorem tailTrace_716426 : CollatzResearch.WordTrace tailWord_716426 prefixEnd_716426 122623630459373071226741 := by
  unfold tailWord_716426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6532550725629608166166283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17420135268345621776443421 6532550725629608166166283)
  ·
    refine ⟨9798826088444412249249425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6532550725629608166166283 9798826088444412249249425)
    ·
      refine ⟨7349119566333309186937069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9798826088444412249249425 7349119566333309186937069)
      ·
        refine ⟨2755919837374990945101401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7349119566333309186937069 2755919837374990945101401)
        ·
          refine ⟨2066939878031243208826051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2755919837374990945101401 2066939878031243208826051)
          ·
            refine ⟨3100409817046864813239077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2066939878031243208826051 3100409817046864813239077)
            ·
              refine ⟨581326840696287152482327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3100409817046864813239077 581326840696287152482327)
              ·
                refine ⟨871990261044430728723491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581326840696287152482327 871990261044430728723491)
                ·
                  refine ⟨1307985391566646093085237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871990261044430728723491 1307985391566646093085237)
                  ·
                    refine ⟨122623630459373071226741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1307985391566646093085237 122623630459373071226741)
                    ·
                      rfl

theorem cell23_716426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_716426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716426 prefixEnd_716426 := by exact prefixLift 716426
  have htrace : WordTrace (prefixWord ++ tailWord_716426) baseStart_716426 baseEnd_716426 := by
    simpa [prefixWord, tailWord_716426, baseEnd_716426] using wordTrace_append hprefix tailTrace_716426
  have hstable : (prefixWord ++ tailWord_716426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716426).length < 2 ^ (prefixWord ++ tailWord_716426).sum := by decide
  have hdescent : baseEnd_716426 < baseStart_716426 := by decide
  rcases family_descends (prefixWord ++ tailWord_716426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716439 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 4, 4]
def baseStart_716439 : Nat := 118140960795 + 716439 * 2 ^ 59
def prefixEnd_716439 : Nat := 4983230072969 + 3 ^ 40 * 716439 * 2
def baseEnd_716439 : Nat := 122625855542209220939221

theorem tailTrace_716439 : CollatzResearch.WordTrace tailWord_716439 prefixEnd_716439 122625855542209220939221 := by
  unfold tailWord_716439
  simp only [CollatzResearch.WordTrace]
  refine ⟨26130677051471335884888371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17420451367647557256592247 26130677051471335884888371)
  ·
    refine ⟨39196015577207003827332557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26130677051471335884888371 39196015577207003827332557)
    ·
      refine ⟨14698505841452626435249709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39196015577207003827332557 14698505841452626435249709)
      ·
        refine ⟨5511939690544734913218641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14698505841452626435249709 5511939690544734913218641)
        ·
          refine ⟨4133954767908551184913981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5511939690544734913218641 4133954767908551184913981)
          ·
            refine ⟨1550233037965706694342743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4133954767908551184913981 1550233037965706694342743)
            ·
              refine ⟨2325349556948560041514115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1550233037965706694342743 2325349556948560041514115)
              ·
                refine ⟨3488024335422840062271173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2325349556948560041514115 3488024335422840062271173)
                ·
                  refine ⟨654004562891782511675845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3488024335422840062271173 654004562891782511675845)
                  ·
                    refine ⟨122625855542209220939221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 654004562891782511675845 122625855542209220939221)
                    ·
                      rfl

theorem cell23_716439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_716439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716439 prefixEnd_716439 := by exact prefixLift 716439
  have htrace : WordTrace (prefixWord ++ tailWord_716439) baseStart_716439 baseEnd_716439 := by
    simpa [prefixWord, tailWord_716439, baseEnd_716439] using wordTrace_append hprefix tailTrace_716439
  have hstable : (prefixWord ++ tailWord_716439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716439).length < 2 ^ (prefixWord ++ tailWord_716439).sum := by decide
  have hdescent : baseEnd_716439 < baseStart_716439 := by decide
  rcases family_descends (prefixWord ++ tailWord_716439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716449 : List Nat := [1, 2, 3, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_716449 : Nat := 118140960795 + 716449 * 2 ^ 59
def prefixEnd_716449 : Nat := 4983230072969 + 3 ^ 40 * 716449 * 2
def baseEnd_716449 : Nat := 367882701433172623692617

theorem tailTrace_716449 : CollatzResearch.WordTrace tailWord_716449 prefixEnd_716449 367882701433172623692617 := by
  unfold tailWord_716449
  simp only [CollatzResearch.WordTrace]
  refine ⟨26131041781435107592752401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17420694520956738395168267 26131041781435107592752401)
  ·
    refine ⟨19598281336076330694564301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26131041781435107592752401 19598281336076330694564301)
    ·
      refine ⟨7349355501028624010461613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19598281336076330694564301 7349355501028624010461613)
      ·
        refine ⟨2756008312885734003923105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7349355501028624010461613 2756008312885734003923105)
        ·
          refine ⟨2067006234664300502942329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2756008312885734003923105 2067006234664300502942329)
          ·
            refine ⟨1550254675998225377206747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2067006234664300502942329 1550254675998225377206747)
            ·
              refine ⟨2325382013997338065810121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1550254675998225377206747 2325382013997338065810121)
              ·
                refine ⟨1744036510498003549357591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2325382013997338065810121 1744036510498003549357591)
                ·
                  refine ⟨2616054765747005324036387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1744036510498003549357591 2616054765747005324036387)
                  ·
                    refine ⟨3924082148620507986054581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2616054765747005324036387 3924082148620507986054581)
                    ·
                      refine ⟨367882701433172623692617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3924082148620507986054581 367882701433172623692617)
                      ·
                        rfl

theorem cell23_716449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_716449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716449 prefixEnd_716449 := by exact prefixLift 716449
  have htrace : WordTrace (prefixWord ++ tailWord_716449) baseStart_716449 baseEnd_716449 := by
    simpa [prefixWord, tailWord_716449, baseEnd_716449] using wordTrace_append hprefix tailTrace_716449
  have hstable : (prefixWord ++ tailWord_716449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716449).length < 2 ^ (prefixWord ++ tailWord_716449).sum := by decide
  have hdescent : baseEnd_716449 < baseStart_716449 := by decide
  rcases family_descends (prefixWord ++ tailWord_716449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716469 : List Nat := [1, 3, 3, 3, 2, 1, 1, 9]
def baseStart_716469 : Nat := 118140960795 + 716469 * 2 ^ 59
def prefixEnd_716469 : Nat := 4983230072969 + 3 ^ 40 * 716469 * 2
def baseEnd_716469 : Nat := 13625665594306020201575

theorem tailTrace_716469 : CollatzResearch.WordTrace tailWord_716469 prefixEnd_716469 13625665594306020201575 := by
  unfold tailWord_716469
  simp only [CollatzResearch.WordTrace]
  refine ⟨26131771241362651008480461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17421180827575100672320307 26131771241362651008480461)
  ·
    refine ⟨9799414215510994128180173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26131771241362651008480461 9799414215510994128180173)
    ·
      refine ⟨3674780330816622798067565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9799414215510994128180173 3674780330816622798067565)
      ·
        refine ⟨1378042624056233549275337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3674780330816622798067565 1378042624056233549275337)
        ·
          refine ⟨1033531968042175161956503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1378042624056233549275337 1033531968042175161956503)
          ·
            refine ⟨1550297952063262742934755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033531968042175161956503 1550297952063262742934755)
            ·
              refine ⟨2325446928094894114402133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1550297952063262742934755 2325446928094894114402133)
              ·
                refine ⟨13625665594306020201575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2325446928094894114402133 13625665594306020201575)
                ·
                  rfl

theorem cell23_716469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 9].length) (baseStart_716469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716469 prefixEnd_716469 := by exact prefixLift 716469
  have htrace : WordTrace (prefixWord ++ tailWord_716469) baseStart_716469 baseEnd_716469 := by
    simpa [prefixWord, tailWord_716469, baseEnd_716469] using wordTrace_append hprefix tailTrace_716469
  have hstable : (prefixWord ++ tailWord_716469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716469).length < 2 ^ (prefixWord ++ tailWord_716469).sum := by decide
  have hdescent : baseEnd_716469 < baseStart_716469 := by decide
  rcases family_descends (prefixWord ++ tailWord_716469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716479 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 6, 1, 3]
def baseStart_716479 : Nat := 118140960795 + 716479 * 2 ^ 59
def prefixEnd_716479 : Nat := 4983230072969 + 3 ^ 40 * 716479 * 2
def baseEnd_716479 : Nat := 367898105852807506317479

theorem tailTrace_716479 : CollatzResearch.WordTrace tailWord_716479 prefixEnd_716479 367898105852807506317479 := by
  unfold tailWord_716479
  simp only [CollatzResearch.WordTrace]
  refine ⟨26132135971326422716344491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17421423980884281810896327 26132135971326422716344491)
  ·
    refine ⟨39198203956989634074516737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26132135971326422716344491 39198203956989634074516737)
    ·
      refine ⟨29398652967742225555887553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39198203956989634074516737 29398652967742225555887553)
      ·
        refine ⟨22048989725806669166915665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29398652967742225555887553 22048989725806669166915665)
        ·
          refine ⟨16536742294355001875186749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22048989725806669166915665 16536742294355001875186749)
          ·
            refine ⟨6201278360383125703195031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16536742294355001875186749 6201278360383125703195031)
            ·
              refine ⟨9301917540574688554792547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6201278360383125703195031 9301917540574688554792547)
              ·
                refine ⟨13952876310862032832188821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9301917540574688554792547 13952876310862032832188821)
                ·
                  refine ⟨654041077071657789008851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13952876310862032832188821 654041077071657789008851)
                  ·
                    refine ⟨981061615607486683513277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 654041077071657789008851 981061615607486683513277)
                    ·
                      refine ⟨367898105852807506317479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 981061615607486683513277 367898105852807506317479)
                      ·
                        rfl

theorem cell23_716479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 1, 3].length) (baseStart_716479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716479 prefixEnd_716479 := by exact prefixLift 716479
  have htrace : WordTrace (prefixWord ++ tailWord_716479) baseStart_716479 baseEnd_716479 := by
    simpa [prefixWord, tailWord_716479, baseEnd_716479] using wordTrace_append hprefix tailTrace_716479
  have hstable : (prefixWord ++ tailWord_716479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716479).length < 2 ^ (prefixWord ++ tailWord_716479).sum := by decide
  have hdescent : baseEnd_716479 < baseStart_716479 := by decide
  rcases family_descends (prefixWord ++ tailWord_716479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716486 : List Nat := [6, 1, 2, 1, 1, 1, 11]
def baseStart_716486 : Nat := 118140960795 + 716486 * 2 ^ 59
def prefixEnd_716486 : Nat := 4983230072969 + 3 ^ 40 * 716486 * 2
def baseEnd_716486 : Nat := 4541996298980110850987

theorem tailTrace_716486 : CollatzResearch.WordTrace tailWord_716486 prefixEnd_716486 4541996298980110850987 := by
  unfold tailWord_716486
  simp only [CollatzResearch.WordTrace]
  refine ⟨816637227571908215995291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17421594188200708607899541 816637227571908215995291)
  ·
    refine ⟨1224955841357862323992937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 816637227571908215995291 1224955841357862323992937)
    ·
      refine ⟨918716881018396742994703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1224955841357862323992937 918716881018396742994703)
      ·
        refine ⟨1378075321527595114492055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 918716881018396742994703 1378075321527595114492055)
        ·
          refine ⟨2067112982291392671738083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1378075321527595114492055 2067112982291392671738083)
          ·
            refine ⟨3100669473437089007607125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2067112982291392671738083 3100669473437089007607125)
            ·
              refine ⟨4541996298980110850987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3100669473437089007607125 4541996298980110850987)
              ·
                rfl

theorem cell23_716486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 11].length) (baseStart_716486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716486 prefixEnd_716486 := by exact prefixLift 716486
  have htrace : WordTrace (prefixWord ++ tailWord_716486) baseStart_716486 baseEnd_716486 := by
    simpa [prefixWord, tailWord_716486, baseEnd_716486] using wordTrace_append hprefix tailTrace_716486
  have hstable : (prefixWord ++ tailWord_716486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716486).length < 2 ^ (prefixWord ++ tailWord_716486).sum := by decide
  have hdescent : baseEnd_716486 < baseStart_716486 := by decide
  rcases family_descends (prefixWord ++ tailWord_716486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716512 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 2, 6]
def baseStart_716512 : Nat := 118140960795 + 716512 * 2 ^ 59
def prefixEnd_716512 : Nat := 4983230072969 + 3 ^ 40 * 716512 * 2
def baseEnd_716512 : Nat := 122638350238135292401609

theorem tailTrace_716512 : CollatzResearch.WordTrace tailWord_716512 prefixEnd_716512 122638350238135292401609 := by
  unfold tailWord_716512
  simp only [CollatzResearch.WordTrace]
  refine ⟨13066669790103434676147895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17422226386804579568197193 13066669790103434676147895)
  ·
    refine ⟨19600004685155152014221843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13066669790103434676147895 19600004685155152014221843)
    ·
      refine ⟨29400007027732728021332765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19600004685155152014221843 29400007027732728021332765)
      ·
        refine ⟨11025002635399773007999787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29400007027732728021332765 11025002635399773007999787)
        ·
          refine ⟨16537503953099659511999681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11025002635399773007999787 16537503953099659511999681)
          ·
            refine ⟨12403127964824744633999761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16537503953099659511999681 12403127964824744633999761)
            ·
              refine ⟨9302345973618558475499821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12403127964824744633999761 9302345973618558475499821)
              ·
                refine ⟨3488379740106959428312433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9302345973618558475499821 3488379740106959428312433)
                ·
                  refine ⟨2616284805080219571234325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3488379740106959428312433 2616284805080219571234325)
                  ·
                    refine ⟨122638350238135292401609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2616284805080219571234325 122638350238135292401609)
                    ·
                      rfl

theorem cell23_716512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 2, 6].length) (baseStart_716512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716512 prefixEnd_716512 := by exact prefixLift 716512
  have htrace : WordTrace (prefixWord ++ tailWord_716512) baseStart_716512 baseEnd_716512 := by
    simpa [prefixWord, tailWord_716512, baseEnd_716512] using wordTrace_append hprefix tailTrace_716512
  have hstable : (prefixWord ++ tailWord_716512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716512).length < 2 ^ (prefixWord ++ tailWord_716512).sum := by decide
  have hdescent : baseEnd_716512 < baseStart_716512 := by decide
  rcases family_descends (prefixWord ++ tailWord_716512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716513 : List Nat := [1, 2, 3, 1, 5, 1, 1, 3, 2, 1, 3]
def baseStart_716513 : Nat := 118140960795 + 716513 * 2 ^ 59
def prefixEnd_716513 : Nat := 4983230072969 + 3 ^ 40 * 716513 * 2
def baseEnd_716513 : Nat := 367915564195060373292323

theorem tailTrace_716513 : CollatzResearch.WordTrace tailWord_716513 prefixEnd_716513 367915564195060373292323 := by
  unfold tailWord_716513
  simp only [CollatzResearch.WordTrace]
  refine ⟨26133376053203246523082193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17422250702135497682054795 26133376053203246523082193)
  ·
    refine ⟨19600032039902434892311645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26133376053203246523082193 19600032039902434892311645)
    ·
      refine ⟨7350012014963413084616867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19600032039902434892311645 7350012014963413084616867)
      ·
        refine ⟨11025018022445119626925301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7350012014963413084616867 11025018022445119626925301)
        ·
          refine ⟨1033595439604229965024247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11025018022445119626925301 1033595439604229965024247)
          ·
            refine ⟨1550393159406344947536371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033595439604229965024247 1550393159406344947536371)
            ·
              refine ⟨2325589739109517421304557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1550393159406344947536371 2325589739109517421304557)
              ·
                refine ⟨872096152166069032989209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2325589739109517421304557 872096152166069032989209)
                ·
                  refine ⟨654072114124551774741907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 872096152166069032989209 654072114124551774741907)
                  ·
                    refine ⟨981108171186827662112861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 654072114124551774741907 981108171186827662112861)
                    ·
                      refine ⟨367915564195060373292323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 981108171186827662112861 367915564195060373292323)
                      ·
                        rfl

theorem cell23_716513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_716513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716513 prefixEnd_716513 := by exact prefixLift 716513
  have htrace : WordTrace (prefixWord ++ tailWord_716513) baseStart_716513 baseEnd_716513 := by
    simpa [prefixWord, tailWord_716513, baseEnd_716513] using wordTrace_append hprefix tailTrace_716513
  have hstable : (prefixWord ++ tailWord_716513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716513).length < 2 ^ (prefixWord ++ tailWord_716513).sum := by decide
  have hdescent : baseEnd_716513 < baseStart_716513 := by decide
  rcases family_descends (prefixWord ++ tailWord_716513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716536 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 4, 2, 2]
def baseStart_716536 : Nat := 118140960795 + 716536 * 2 ^ 59
def prefixEnd_716536 : Nat := 4983230072969 + 3 ^ 40 * 716536 * 2
def baseEnd_716536 : Nat := 367927374250113783304717

theorem tailTrace_716536 : CollatzResearch.WordTrace tailWord_716536 prefixEnd_716536 367927374250113783304717 := by
  unfold tailWord_716536
  simp only [CollatzResearch.WordTrace]
  refine ⟨13067107466059960725584731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17422809954746614300779641 13067107466059960725584731)
  ·
    refine ⟨19600661199089941088377097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13067107466059960725584731 19600661199089941088377097)
    ·
      refine ⟨14700495899317455816282823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19600661199089941088377097 14700495899317455816282823)
      ·
        refine ⟨22050743848976183724424235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14700495899317455816282823 22050743848976183724424235)
        ·
          refine ⟨33076115773464275586636353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22050743848976183724424235 33076115773464275586636353)
          ·
            refine ⟨24807086830098206689977265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33076115773464275586636353 24807086830098206689977265)
            ·
              refine ⟨18605315122573655017482949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24807086830098206689977265 18605315122573655017482949)
              ·
                refine ⟨3488496585482560315778053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18605315122573655017482949 3488496585482560315778053)
                ·
                  refine ⟨654093109777980059208385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3488496585482560315778053 654093109777980059208385)
                  ·
                    refine ⟨490569832333485044406289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 654093109777980059208385 490569832333485044406289)
                    ·
                      refine ⟨367927374250113783304717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 490569832333485044406289 367927374250113783304717)
                      ·
                        rfl

theorem cell23_716536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 4, 2, 2].length) (baseStart_716536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716536 prefixEnd_716536 := by exact prefixLift 716536
  have htrace : WordTrace (prefixWord ++ tailWord_716536) baseStart_716536 baseEnd_716536 := by
    simpa [prefixWord, tailWord_716536, baseEnd_716536] using wordTrace_append hprefix tailTrace_716536
  have hstable : (prefixWord ++ tailWord_716536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716536).length < 2 ^ (prefixWord ++ tailWord_716536).sum := by decide
  have hdescent : baseEnd_716536 < baseStart_716536 := by decide
  rcases family_descends (prefixWord ++ tailWord_716536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716670 : List Nat := [4, 2, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_716670 : Nat := 118140960795 + 716670 * 2 ^ 59
def prefixEnd_716670 : Nat := 4983230072969 + 3 ^ 40 * 716670 * 2
def baseEnd_716670 : Nat := 122665393552605419676367

theorem tailTrace_716670 : CollatzResearch.WordTrace tailWord_716670 prefixEnd_716670 122665393552605419676367 := by
  unfold tailWord_716670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3267387789204307792068433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17426068209089641557698309 3267387789204307792068433)
  ·
    refine ⟨2450540841903230844051325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3267387789204307792068433 2450540841903230844051325)
    ·
      refine ⟨918952815713711566519247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2450540841903230844051325 918952815713711566519247)
      ·
        refine ⟨1378429223570567349778871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 918952815713711566519247 1378429223570567349778871)
        ·
          refine ⟨2067643835355851024668307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1378429223570567349778871 2067643835355851024668307)
          ·
            refine ⟨3101465753033776537002461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2067643835355851024668307 3101465753033776537002461)
            ·
              refine ⟨1163049657387666201375923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3101465753033776537002461 1163049657387666201375923)
              ·
                refine ⟨1744574486081499302063885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163049657387666201375923 1744574486081499302063885)
                ·
                  refine ⟨654215432280562238273957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1744574486081499302063885 654215432280562238273957)
                  ·
                    refine ⟨122665393552605419676367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 654215432280562238273957 122665393552605419676367)
                    ·
                      rfl

theorem cell23_716670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_716670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716670 prefixEnd_716670 := by exact prefixLift 716670
  have htrace : WordTrace (prefixWord ++ tailWord_716670) baseStart_716670 baseEnd_716670 := by
    simpa [prefixWord, tailWord_716670, baseEnd_716670] using wordTrace_append hprefix tailTrace_716670
  have hstable : (prefixWord ++ tailWord_716670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716670).length < 2 ^ (prefixWord ++ tailWord_716670).sum := by decide
  have hdescent : baseEnd_716670 < baseStart_716670 := by decide
  rcases family_descends (prefixWord ++ tailWord_716670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716736 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 3]
def baseStart_716736 : Nat := 118140960795 + 716736 * 2 ^ 59
def prefixEnd_716736 : Nat := 4983230072969 + 3 ^ 40 * 716736 * 2
def baseEnd_716736 : Nat := 368030070381013000803797

theorem tailTrace_716736 : CollatzResearch.WordTrace tailWord_716736 prefixEnd_716736 368030070381013000803797 := by
  unfold tailWord_716736
  simp only [CollatzResearch.WordTrace]
  refine ⟨13070754765697677804225031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17427673020930237072300041 13070754765697677804225031)
  ·
    refine ⟨19606132148546516706337547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13070754765697677804225031 19606132148546516706337547)
    ·
      refine ⟨29409198222819775059506321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19606132148546516706337547 29409198222819775059506321)
      ·
        refine ⟨22056898667114831294629741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29409198222819775059506321 22056898667114831294629741)
        ·
          refine ⟨8271337000168061735486153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22056898667114831294629741 8271337000168061735486153)
          ·
            refine ⟨6203502750126046301614615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8271337000168061735486153 6203502750126046301614615)
            ·
              refine ⟨9305254125189069452421923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6203502750126046301614615 9305254125189069452421923)
              ·
                refine ⟨13957881187783604178632885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9305254125189069452421923 13957881187783604178632885)
                ·
                  refine ⟨1308551361354712891746833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13957881187783604178632885 1308551361354712891746833)
                  ·
                    refine ⟨981413521016034668810125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1308551361354712891746833 981413521016034668810125)
                    ·
                      refine ⟨368030070381013000803797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 981413521016034668810125 368030070381013000803797)
                      ·
                        rfl

theorem cell23_716736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_716736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716736 prefixEnd_716736 := by exact prefixLift 716736
  have htrace : WordTrace (prefixWord ++ tailWord_716736) baseStart_716736 baseEnd_716736 := by
    simpa [prefixWord, tailWord_716736, baseEnd_716736] using wordTrace_append hprefix tailTrace_716736
  have hstable : (prefixWord ++ tailWord_716736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716736).length < 2 ^ (prefixWord ++ tailWord_716736).sum := by decide
  have hdescent : baseEnd_716736 < baseStart_716736 := by decide
  rcases family_descends (prefixWord ++ tailWord_716736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716746 : List Nat := [3, 1, 2, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_716746 : Nat := 118140960795 + 716746 * 2 ^ 59
def prefixEnd_716746 : Nat := 4983230072969 + 3 ^ 40 * 716746 * 2
def baseEnd_716746 : Nat := 368035205187557961678751

theorem tailTrace_716746 : CollatzResearch.WordTrace tailWord_716746 prefixEnd_716746 368035205187557961678751 := by
  unfold tailWord_716746
  simp only [CollatzResearch.WordTrace]
  refine ⟨6535468565339781829078523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17427916174239418210876061 6535468565339781829078523)
  ·
    refine ⟨9803202848009672743617785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6535468565339781829078523 9803202848009672743617785)
    ·
      refine ⟨7352402136007254557713339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9803202848009672743617785 7352402136007254557713339)
      ·
        refine ⟨11028603204010881836570009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7352402136007254557713339 11028603204010881836570009)
        ·
          refine ⟨8271452403008161377427507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11028603204010881836570009 8271452403008161377427507)
          ·
            refine ⟨12407178604512242066141261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8271452403008161377427507 12407178604512242066141261)
            ·
              refine ⟨4652691976692090774802973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12407178604512242066141261 4652691976692090774802973)
              ·
                refine ⟨1744759491259534040551115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4652691976692090774802973 1744759491259534040551115)
                ·
                  refine ⟨2617139236889301060826673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1744759491259534040551115 2617139236889301060826673)
                  ·
                    refine ⟨1962854427666975795620005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2617139236889301060826673 1962854427666975795620005)
                    ·
                      refine ⟨368035205187557961678751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1962854427666975795620005 368035205187557961678751)
                      ·
                        rfl

theorem cell23_716746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_716746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716746 prefixEnd_716746 := by exact prefixLift 716746
  have htrace : WordTrace (prefixWord ++ tailWord_716746) baseStart_716746 baseEnd_716746 := by
    simpa [prefixWord, tailWord_716746, baseEnd_716746] using wordTrace_append hprefix tailTrace_716746
  have hstable : (prefixWord ++ tailWord_716746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716746).length < 2 ^ (prefixWord ++ tailWord_716746).sum := by decide
  have hdescent : baseEnd_716746 < baseStart_716746 := by decide
  rcases family_descends (prefixWord ++ tailWord_716746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716750 : List Nat := [4, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2]
def baseStart_716750 : Nat := 118140960795 + 716750 * 2 ^ 59
def prefixEnd_716750 : Nat := 4983230072969 + 3 ^ 40 * 716750 * 2
def baseEnd_716750 : Nat := 368037259110175946028733

theorem tailTrace_716750 : CollatzResearch.WordTrace tailWord_716750 prefixEnd_716750 368037259110175946028733 := by
  unfold tailWord_716750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3267752519168079499932463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17428013435563090666306469 3267752519168079499932463)
  ·
    refine ⟨4901628778752119249898695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3267752519168079499932463 4901628778752119249898695)
    ·
      refine ⟨7352443168128178874848043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4901628778752119249898695 7352443168128178874848043)
      ·
        refine ⟨11028664752192268312272065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7352443168128178874848043 11028664752192268312272065)
        ·
          refine ⟨8271498564144201234204049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11028664752192268312272065 8271498564144201234204049)
          ·
            refine ⟨6203623923108150925653037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8271498564144201234204049 6203623923108150925653037)
            ·
              refine ⟨2326358971165556597119889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6203623923108150925653037 2326358971165556597119889)
              ·
                refine ⟨1744769228374167447839917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2326358971165556597119889 1744769228374167447839917)
                ·
                  refine ⟨654288460640312792939969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1744769228374167447839917 654288460640312792939969)
                  ·
                    refine ⟨490716345480234594704977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 654288460640312792939969 490716345480234594704977)
                    ·
                      refine ⟨368037259110175946028733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 490716345480234594704977 368037259110175946028733)
                      ·
                        rfl

theorem cell23_716750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_716750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716750 prefixEnd_716750 := by exact prefixLift 716750
  have htrace : WordTrace (prefixWord ++ tailWord_716750) baseStart_716750 baseEnd_716750 := by
    simpa [prefixWord, tailWord_716750, baseEnd_716750] using wordTrace_append hprefix tailTrace_716750
  have hstable : (prefixWord ++ tailWord_716750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716750).length < 2 ^ (prefixWord ++ tailWord_716750).sum := by decide
  have hdescent : baseEnd_716750 < baseStart_716750 := by decide
  rcases family_descends (prefixWord ++ tailWord_716750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716754 : List Nat := [3, 2, 2, 3, 3, 1, 1, 1, 2, 3, 2]
def baseStart_716754 : Nat := 118140960795 + 716754 * 2 ^ 59
def prefixEnd_716754 : Nat := 4983230072969 + 3 ^ 40 * 716754 * 2
def baseEnd_716754 : Nat := 368039313032793930378715

theorem tailTrace_716754 : CollatzResearch.WordTrace tailWord_716754 prefixEnd_716754 368039313032793930378715 := by
  unfold tailWord_716754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6535541511332536170651329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17428110696886763121736877 6535541511332536170651329)
  ·
    refine ⟨4901656133499402127988497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6535541511332536170651329 4901656133499402127988497)
    ·
      refine ⟨3676242100124551595991373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4901656133499402127988497 3676242100124551595991373)
      ·
        refine ⟨1378590787546706848496765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3676242100124551595991373 1378590787546706848496765)
        ·
          refine ⟨516971545330015068186287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1378590787546706848496765 516971545330015068186287)
          ·
            refine ⟨775457317995022602279431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516971545330015068186287 775457317995022602279431)
            ·
              refine ⟨1163185976992533903419147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775457317995022602279431 1163185976992533903419147)
              ·
                refine ⟨1744778965488800855128721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163185976992533903419147 1744778965488800855128721)
                ·
                  refine ⟨1308584224116600641346541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1744778965488800855128721 1308584224116600641346541)
                  ·
                    refine ⟨490719084043725240504953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1308584224116600641346541 490719084043725240504953)
                    ·
                      refine ⟨368039313032793930378715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 490719084043725240504953 368039313032793930378715)
                      ·
                        rfl

theorem cell23_716754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_716754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716754 prefixEnd_716754 := by exact prefixLift 716754
  have htrace : WordTrace (prefixWord ++ tailWord_716754) baseStart_716754 baseEnd_716754 := by
    simpa [prefixWord, tailWord_716754, baseEnd_716754] using wordTrace_append hprefix tailTrace_716754
  have hstable : (prefixWord ++ tailWord_716754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716754).length < 2 ^ (prefixWord ++ tailWord_716754).sum := by decide
  have hdescent : baseEnd_716754 < baseStart_716754 := by decide
  rcases family_descends (prefixWord ++ tailWord_716754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716767 : List Nat := [1, 1, 2, 3, 4, 1, 1, 5, 1, 2, 2]
def baseStart_716767 : Nat := 118140960795 + 716767 * 2 ^ 59
def prefixEnd_716767 : Nat := 4983230072969 + 3 ^ 40 * 716767 * 2
def baseEnd_716767 : Nat := 368045988281302379516155

theorem tailTrace_716767 : CollatzResearch.WordTrace tailWord_716767 prefixEnd_716767 368045988281302379516155 := by
  unfold tailWord_716767
  simp only [CollatzResearch.WordTrace]
  refine ⟨26142640194283047902828555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17428426796188698601885703 26142640194283047902828555)
  ·
    refine ⟨39213960291424571854242833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26142640194283047902828555 39213960291424571854242833)
    ·
      refine ⟨29410470218568428890682125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39213960291424571854242833 29410470218568428890682125)
      ·
        refine ⟨11028926331963160834005797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29410470218568428890682125 11028926331963160834005797)
        ·
          refine ⟨2067923687243092656376087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11028926331963160834005797 2067923687243092656376087)
          ·
            refine ⟨3101885530864638984564131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2067923687243092656376087 3101885530864638984564131)
            ·
              refine ⟨4652828296296958476846197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3101885530864638984564131 4652828296296958476846197)
              ·
                refine ⟨436202652777839857204331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4652828296296958476846197 436202652777839857204331)
                ·
                  refine ⟨654303979166759785806497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 436202652777839857204331 654303979166759785806497)
                  ·
                    refine ⟨490727984375069839354873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 654303979166759785806497 490727984375069839354873)
                    ·
                      refine ⟨368045988281302379516155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 490727984375069839354873 368045988281302379516155)
                      ·
                        rfl

theorem cell23_716767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 1, 2, 2].length) (baseStart_716767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716767 prefixEnd_716767 := by exact prefixLift 716767
  have htrace : WordTrace (prefixWord ++ tailWord_716767) baseStart_716767 baseEnd_716767 := by
    simpa [prefixWord, tailWord_716767, baseEnd_716767] using wordTrace_append hprefix tailTrace_716767
  have hstable : (prefixWord ++ tailWord_716767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716767).length < 2 ^ (prefixWord ++ tailWord_716767).sum := by decide
  have hdescent : baseEnd_716767 < baseStart_716767 := by decide
  rcases family_descends (prefixWord ++ tailWord_716767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716783 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 4, 1, 3]
def baseStart_716783 : Nat := 118140960795 + 716783 * 2 ^ 59
def prefixEnd_716783 : Nat := 4983230072969 + 3 ^ 40 * 716783 * 2
def baseEnd_716783 : Nat := 368054203971774316916081

theorem tailTrace_716783 : CollatzResearch.WordTrace tailWord_716783 prefixEnd_716783 368054203971774316916081 := by
  unfold tailWord_716783
  simp only [CollatzResearch.WordTrace]
  refine ⟨26143223762225082635411003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17428815841483388423607335 26143223762225082635411003)
  ·
    refine ⟨39214835643337623953116505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26143223762225082635411003 39214835643337623953116505)
    ·
      refine ⟨29411126732503217964837379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39214835643337623953116505 29411126732503217964837379)
      ·
        refine ⟨44116690098754826947256069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29411126732503217964837379 44116690098754826947256069)
        ·
          refine ⟨8271879393516530052610513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44116690098754826947256069 8271879393516530052610513)
          ·
            refine ⟨6203909545137397539457885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8271879393516530052610513 6203909545137397539457885)
            ·
              refine ⟨2326466079426524077296707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6203909545137397539457885 2326466079426524077296707)
              ·
                refine ⟨3489699119139786115945061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2326466079426524077296707 3489699119139786115945061)
                ·
                  refine ⟨654318584838709896739699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3489699119139786115945061 654318584838709896739699)
                  ·
                    refine ⟨981477877258064845109549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 654318584838709896739699 981477877258064845109549)
                    ·
                      refine ⟨368054203971774316916081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 981477877258064845109549 368054203971774316916081)
                      ·
                        rfl

theorem cell23_716783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 1, 3].length) (baseStart_716783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716783 prefixEnd_716783 := by exact prefixLift 716783
  have htrace : WordTrace (prefixWord ++ tailWord_716783) baseStart_716783 baseEnd_716783 := by
    simpa [prefixWord, tailWord_716783, baseEnd_716783] using wordTrace_append hprefix tailTrace_716783
  have hstable : (prefixWord ++ tailWord_716783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716783).length < 2 ^ (prefixWord ++ tailWord_716783).sum := by decide
  have hdescent : baseEnd_716783 < baseStart_716783 := by decide
  rcases family_descends (prefixWord ++ tailWord_716783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716826 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5]
def baseStart_716826 : Nat := 118140960795 + 716826 * 2 ^ 59
def prefixEnd_716826 : Nat := 4983230072969 + 3 ^ 40 * 716826 * 2
def baseEnd_716826 : Nat := 368076283639917648678383

theorem tailTrace_716826 : CollatzResearch.WordTrace tailWord_716826 prefixEnd_716826 368076283639917648678383 := by
  unfold tailWord_716826
  simp only [CollatzResearch.WordTrace]
  refine ⟨6536198025267325244806583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17429861400712867319484221 6536198025267325244806583)
  ·
    refine ⟨9804297037900987867209875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6536198025267325244806583 9804297037900987867209875)
    ·
      refine ⟨14706445556851481800814813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9804297037900987867209875 14706445556851481800814813)
      ·
        refine ⟨5514917083819305675305555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14706445556851481800814813 5514917083819305675305555)
        ·
          refine ⟨8272375625728958512958333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5514917083819305675305555 8272375625728958512958333)
          ·
            refine ⟨3102140859648359442359375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8272375625728958512958333 3102140859648359442359375)
            ·
              refine ⟨4653211289472539163539063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3102140859648359442359375 4653211289472539163539063)
              ·
                refine ⟨6979816934208808745308595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4653211289472539163539063 6979816934208808745308595)
                ·
                  refine ⟨10469725401313213117962893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6979816934208808745308595 10469725401313213117962893)
                  ·
                    refine ⟨3926147025492454919236085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10469725401313213117962893 3926147025492454919236085)
                    ·
                      refine ⟨368076283639917648678383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3926147025492454919236085 368076283639917648678383)
                      ·
                        rfl

theorem cell23_716826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_716826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716826 prefixEnd_716826 := by exact prefixLift 716826
  have htrace : WordTrace (prefixWord ++ tailWord_716826) baseStart_716826 baseEnd_716826 := by
    simpa [prefixWord, tailWord_716826, baseEnd_716826] using wordTrace_append hprefix tailTrace_716826
  have hstable : (prefixWord ++ tailWord_716826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716826).length < 2 ^ (prefixWord ++ tailWord_716826).sum := by decide
  have hdescent : baseEnd_716826 < baseStart_716826 := by decide
  rcases family_descends (prefixWord ++ tailWord_716826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716876 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 1, 7]
def baseStart_716876 : Nat := 118140960795 + 716876 * 2 ^ 59
def prefixEnd_716876 : Nat := 4983230072969 + 3 ^ 40 * 716876 * 2
def baseEnd_716876 : Nat := 122700652557547484351051

theorem tailTrace_716876 : CollatzResearch.WordTrace tailWord_716876 prefixEnd_716876 122700652557547484351051 := by
  unfold tailWord_716876
  simp only [CollatzResearch.WordTrace]
  refine ⟨13073307875444079759273241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17431077167258773012364321 13073307875444079759273241)
  ·
    refine ⟨9804980906583059819454931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13073307875444079759273241 9804980906583059819454931)
    ·
      refine ⟨14707471359874589729182397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9804980906583059819454931 14707471359874589729182397)
      ·
        refine ⟨5515301759952971148443399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14707471359874589729182397 5515301759952971148443399)
        ·
          refine ⟨8272952639929456722665099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5515301759952971148443399 8272952639929456722665099)
          ·
            refine ⟨12409428959894185083997649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8272952639929456722665099 12409428959894185083997649)
            ·
              refine ⟨9307071719920638812998237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12409428959894185083997649 9307071719920638812998237)
              ·
                refine ⟨3490151894970239554874339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9307071719920638812998237 3490151894970239554874339)
                ·
                  refine ⟨5235227842455359332311509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3490151894970239554874339 5235227842455359332311509)
                  ·
                    refine ⟨122700652557547484351051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5235227842455359332311509 122700652557547484351051)
                    ·
                      rfl

theorem cell23_716876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_716876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716876 prefixEnd_716876 := by exact prefixLift 716876
  have htrace : WordTrace (prefixWord ++ tailWord_716876) baseStart_716876 baseEnd_716876 := by
    simpa [prefixWord, tailWord_716876, baseEnd_716876] using wordTrace_append hprefix tailTrace_716876
  have hstable : (prefixWord ++ tailWord_716876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716876).length < 2 ^ (prefixWord ++ tailWord_716876).sum := by decide
  have hdescent : baseEnd_716876 < baseStart_716876 := by decide
  rcases family_descends (prefixWord ++ tailWord_716876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716957 : List Nat := [1, 4, 2, 1, 1, 3, 2, 4, 1, 4]
def baseStart_716957 : Nat := 118140960795 + 716957 * 2 ^ 59
def prefixEnd_716957 : Nat := 4983230072969 + 3 ^ 40 * 716957 * 2
def baseEnd_716957 : Nat := 122714516535218878713427

theorem tailTrace_716957 : CollatzResearch.WordTrace tailWord_716957 prefixEnd_716957 122714516535218878713427 := by
  unfold tailWord_716957
  simp only [CollatzResearch.WordTrace]
  refine ⟨26149570063594710352245125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17433046709063140234830083 26149570063594710352245125)
  ·
    refine ⟨4903044386924008191045961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26149570063594710352245125 4903044386924008191045961)
    ·
      refine ⟨3677283290193006143284471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4903044386924008191045961 3677283290193006143284471)
      ·
        refine ⟨5515924935289509214926707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3677283290193006143284471 5515924935289509214926707)
        ·
          refine ⟨8273887402934263822390061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5515924935289509214926707 8273887402934263822390061)
          ·
            refine ⟨3102707776100348933396273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8273887402934263822390061 3102707776100348933396273)
            ·
              refine ⟨2327030832075261700047205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3102707776100348933396273 2327030832075261700047205)
              ·
                refine ⟨436318281014111568758851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2327030832075261700047205 436318281014111568758851)
                ·
                  refine ⟨654477421521167353138277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 436318281014111568758851 654477421521167353138277)
                  ·
                    refine ⟨122714516535218878713427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 654477421521167353138277 122714516535218878713427)
                    ·
                      rfl

theorem cell23_716957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_716957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716957 prefixEnd_716957 := by exact prefixLift 716957
  have htrace : WordTrace (prefixWord ++ tailWord_716957) baseStart_716957 baseEnd_716957 := by
    simpa [prefixWord, tailWord_716957, baseEnd_716957] using wordTrace_append hprefix tailTrace_716957
  have hstable : (prefixWord ++ tailWord_716957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716957).length < 2 ^ (prefixWord ++ tailWord_716957).sum := by decide
  have hdescent : baseEnd_716957 < baseStart_716957 := by decide
  rcases family_descends (prefixWord ++ tailWord_716957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717023 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 3]
def baseStart_717023 : Nat := 118140960795 + 717023 * 2 ^ 59
def prefixEnd_717023 : Nat := 4983230072969 + 3 ^ 40 * 717023 * 2
def baseEnd_717023 : Nat := 368177439328853377914977

theorem tailTrace_717023 : CollatzResearch.WordTrace tailWord_717023 prefixEnd_717023 368177439328853377914977 := by
  unfold tailWord_717023
  simp only [CollatzResearch.WordTrace]
  refine ⟨26151977281355603624147723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17434651520903735749431815 26151977281355603624147723)
  ·
    refine ⟨39227965922033405436221585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26151977281355603624147723 39227965922033405436221585)
    ·
      refine ⟨29420974441525054077166189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39227965922033405436221585 29420974441525054077166189)
      ·
        refine ⟨11032865415571895278937321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29420974441525054077166189 11032865415571895278937321)
        ·
          refine ⟨8274649061678921459202991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11032865415571895278937321 8274649061678921459202991)
          ·
            refine ⟨12411973592518382188804487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8274649061678921459202991 12411973592518382188804487)
            ·
              refine ⟨18617960388777573283206731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12411973592518382188804487 18617960388777573283206731)
              ·
                refine ⟨27926940583166359924810097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18617960388777573283206731 27926940583166359924810097)
                ·
                  refine ⟨20945205437374769943607573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27926940583166359924810097 20945205437374769943607573)
                  ·
                    refine ⟨981806504876942341106605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20945205437374769943607573 981806504876942341106605)
                    ·
                      refine ⟨368177439328853377914977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 981806504876942341106605 368177439328853377914977)
                      ·
                        rfl

theorem cell23_717023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_717023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717023 prefixEnd_717023 := by exact prefixLift 717023
  have htrace : WordTrace (prefixWord ++ tailWord_717023) baseStart_717023 baseEnd_717023 := by
    simpa [prefixWord, tailWord_717023, baseEnd_717023] using wordTrace_append hprefix tailTrace_717023
  have hstable : (prefixWord ++ tailWord_717023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717023).length < 2 ^ (prefixWord ++ tailWord_717023).sum := by decide
  have hdescent : baseEnd_717023 < baseStart_717023 := by decide
  rcases family_descends (prefixWord ++ tailWord_717023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717037 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_717037 : Nat := 118140960795 + 717037 * 2 ^ 59
def prefixEnd_717037 : Nat := 4983230072969 + 3 ^ 40 * 717037 * 2
def baseEnd_717037 : Nat := 368184628058016323139913

theorem tailTrace_717037 : CollatzResearch.WordTrace tailWord_717037 prefixEnd_717037 368184628058016323139913 := by
  unfold tailWord_717037
  simp only [CollatzResearch.WordTrace]
  refine ⟨26152487903304884015157365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17434991935536589343438243 26152487903304884015157365)
  ·
    refine ⟨2451795740934832876421003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26152487903304884015157365 2451795740934832876421003)
    ·
      refine ⟨3677693611402249314631505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2451795740934832876421003 3677693611402249314631505)
      ·
        refine ⟨2758270208551686985973629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3677693611402249314631505 2758270208551686985973629)
        ·
          refine ⟨1034351328206882619740111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2758270208551686985973629 1034351328206882619740111)
          ·
            refine ⟨1551526992310323929610167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034351328206882619740111 1551526992310323929610167)
            ·
              refine ⟨2327290488465485894415251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1551526992310323929610167 2327290488465485894415251)
              ·
                refine ⟨3490935732698228841622877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2327290488465485894415251 3490935732698228841622877)
                ·
                  refine ⟨1309100899761835815608579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3490935732698228841622877 1309100899761835815608579)
                  ·
                    refine ⟨1963651349642753723412869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1309100899761835815608579 1963651349642753723412869)
                    ·
                      refine ⟨368184628058016323139913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1963651349642753723412869 368184628058016323139913)
                      ·
                        rfl

theorem cell23_717037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_717037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717037 prefixEnd_717037 := by exact prefixLift 717037
  have htrace : WordTrace (prefixWord ++ tailWord_717037) baseStart_717037 baseEnd_717037 := by
    simpa [prefixWord, tailWord_717037, baseEnd_717037] using wordTrace_append hprefix tailTrace_717037
  have hstable : (prefixWord ++ tailWord_717037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717037).length < 2 ^ (prefixWord ++ tailWord_717037).sum := by decide
  have hdescent : baseEnd_717037 < baseStart_717037 := by decide
  rcases family_descends (prefixWord ++ tailWord_717037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717050 : List Nat := [3, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4]
def baseStart_717050 : Nat := 118140960795 + 717050 * 2 ^ 59
def prefixEnd_717050 : Nat := 4983230072969 + 3 ^ 40 * 717050 * 2
def baseEnd_717050 : Nat := 368191303306524772277353

theorem tailTrace_717050 : CollatzResearch.WordTrace tailWord_717050 prefixEnd_717050 368191303306524772277353 := by
  unfold tailWord_717050
  simp only [CollatzResearch.WordTrace]
  refine ⟨6538240513064446808845151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17435308034838524823587069 6538240513064446808845151)
  ·
    refine ⟨9807360769596670213267727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6538240513064446808845151 9807360769596670213267727)
    ·
      refine ⟨14711041154395005319901591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9807360769596670213267727 14711041154395005319901591)
      ·
        refine ⟨22066561731592507979852387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14711041154395005319901591 22066561731592507979852387)
        ·
          refine ⟨33099842597388761969778581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22066561731592507979852387 33099842597388761969778581)
          ·
            refine ⟨1551555121752598217333371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33099842597388761969778581 1551555121752598217333371)
            ·
              refine ⟨2327332682628897326000057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1551555121752598217333371 2327332682628897326000057)
              ·
                refine ⟨1745499511971672994500043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2327332682628897326000057 1745499511971672994500043)
                ·
                  refine ⟨2618249267957509491750065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1745499511971672994500043 2618249267957509491750065)
                  ·
                    refine ⟨1963686950968132118812549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2618249267957509491750065 1963686950968132118812549)
                    ·
                      refine ⟨368191303306524772277353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1963686950968132118812549 368191303306524772277353)
                      ·
                        rfl

theorem cell23_717050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_717050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717050 prefixEnd_717050 := by exact prefixLift 717050
  have htrace : WordTrace (prefixWord ++ tailWord_717050) baseStart_717050 baseEnd_717050 := by
    simpa [prefixWord, tailWord_717050, baseEnd_717050] using wordTrace_append hprefix tailTrace_717050
  have hstable : (prefixWord ++ tailWord_717050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717050).length < 2 ^ (prefixWord ++ tailWord_717050).sum := by decide
  have hdescent : baseEnd_717050 < baseStart_717050 := by decide
  rcases family_descends (prefixWord ++ tailWord_717050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717054 : List Nat := [4, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_717054 : Nat := 118140960795 + 717054 * 2 ^ 59
def prefixEnd_717054 : Nat := 4983230072969 + 3 ^ 40 * 717054 * 2
def baseEnd_717054 : Nat := 368193357229142756627335

theorem tailTrace_717054 : CollatzResearch.WordTrace tailWord_717054 prefixEnd_717054 368193357229142756627335 := by
  unfold tailWord_717054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3269138493030411989815777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17435405296162197279017477 3269138493030411989815777)
  ·
    refine ⟨2451853869772808992361833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3269138493030411989815777 2451853869772808992361833)
    ·
      refine ⟨1838890402329606744271375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2451853869772808992361833 1838890402329606744271375)
      ·
        refine ⟨2758335603494410116407063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1838890402329606744271375 2758335603494410116407063)
        ·
          refine ⟨4137503405241615174610595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2758335603494410116407063 4137503405241615174610595)
          ·
            refine ⟨6206255107862422761915893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4137503405241615174610595 6206255107862422761915893)
            ·
              refine ⟨581836416362102133929615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6206255107862422761915893 581836416362102133929615)
              ·
                refine ⟨872754624543153200894423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581836416362102133929615 872754624543153200894423)
                ·
                  refine ⟨1309131936814729801341635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 872754624543153200894423 1309131936814729801341635)
                  ·
                    refine ⟨1963697905222094702012453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1309131936814729801341635 1963697905222094702012453)
                    ·
                      refine ⟨368193357229142756627335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1963697905222094702012453 368193357229142756627335)
                      ·
                        rfl

theorem cell23_717054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_717054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717054 prefixEnd_717054 := by exact prefixLift 717054
  have htrace : WordTrace (prefixWord ++ tailWord_717054) baseStart_717054 baseEnd_717054 := by
    simpa [prefixWord, tailWord_717054, baseEnd_717054] using wordTrace_append hprefix tailTrace_717054
  have hstable : (prefixWord ++ tailWord_717054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717054).length < 2 ^ (prefixWord ++ tailWord_717054).sum := by decide
  have hdescent : baseEnd_717054 < baseStart_717054 := by decide
  rcases family_descends (prefixWord ++ tailWord_717054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717060 : List Nat := [2, 3, 2, 2, 4, 10]
def baseStart_717060 : Nat := 118140960795 + 717060 * 2 ^ 59
def prefixEnd_717060 : Nat := 4983230072969 + 3 ^ 40 * 717060 * 2
def baseEnd_717060 : Nat := 1515211679477653222849

theorem tailTrace_717060 : CollatzResearch.WordTrace tailWord_717060 prefixEnd_717060 1515211679477653222849 := by
  unfold tailWord_717060
  simp only [CollatzResearch.WordTrace]
  refine ⟨13076663391110779471622317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17435551188147705962163089 13076663391110779471622317)
  ·
    refine ⟨4903748771666542301858369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13076663391110779471622317 4903748771666542301858369)
    ·
      refine ⟨3677811578749906726393777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4903748771666542301858369 3677811578749906726393777)
      ·
        refine ⟨2758358684062430044795333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3677811578749906726393777 2758358684062430044795333)
        ·
          refine ⟨517192253261705633399125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2758358684062430044795333 517192253261705633399125)
          ·
            refine ⟨1515211679477653222849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 517192253261705633399125 1515211679477653222849)
            ·
              rfl

theorem cell23_717060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 10].length) (baseStart_717060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717060 prefixEnd_717060 := by exact prefixLift 717060
  have htrace : WordTrace (prefixWord ++ tailWord_717060) baseStart_717060 baseEnd_717060 := by
    simpa [prefixWord, tailWord_717060, baseEnd_717060] using wordTrace_append hprefix tailTrace_717060
  have hstable : (prefixWord ++ tailWord_717060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717060).length < 2 ^ (prefixWord ++ tailWord_717060).sum := by decide
  have hdescent : baseEnd_717060 < baseStart_717060 := by decide
  rcases family_descends (prefixWord ++ tailWord_717060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717070 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3]
def baseStart_717070 : Nat := 118140960795 + 717070 * 2 ^ 59
def prefixEnd_717070 : Nat := 4983230072969 + 3 ^ 40 * 717070 * 2
def baseEnd_717070 : Nat := 368201572919614694027261

theorem tailTrace_717070 : CollatzResearch.WordTrace tailWord_717070 prefixEnd_717070 368201572919614694027261 := by
  unfold tailWord_717070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3269211439023166331388583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17435794341456887100739109 3269211439023166331388583)
  ·
    refine ⟨4903817158534749497082875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3269211439023166331388583 4903817158534749497082875)
    ·
      refine ⟨7355725737802124245624313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4903817158534749497082875 7355725737802124245624313)
      ·
        refine ⟨5516794303351593184218235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7355725737802124245624313 5516794303351593184218235)
        ·
          refine ⟨8275191455027389776327353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5516794303351593184218235 8275191455027389776327353)
          ·
            refine ⟨6206393591270542332245515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8275191455027389776327353 6206393591270542332245515)
            ·
              refine ⟨9309590386905813498368273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6206393591270542332245515 9309590386905813498368273)
              ·
                refine ⟨6982192790179360123776205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9309590386905813498368273 6982192790179360123776205)
                ·
                  refine ⟨2618322296317260046416077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6982192790179360123776205 2618322296317260046416077)
                  ·
                    refine ⟨981870861118972517406029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2618322296317260046416077 981870861118972517406029)
                    ·
                      refine ⟨368201572919614694027261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 981870861118972517406029 368201572919614694027261)
                      ·
                        rfl

theorem cell23_717070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_717070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717070 prefixEnd_717070 := by exact prefixLift 717070
  have htrace : WordTrace (prefixWord ++ tailWord_717070) baseStart_717070 baseEnd_717070 := by
    simpa [prefixWord, tailWord_717070, baseEnd_717070] using wordTrace_append hprefix tailTrace_717070
  have hstable : (prefixWord ++ tailWord_717070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717070).length < 2 ^ (prefixWord ++ tailWord_717070).sum := by decide
  have hdescent : baseEnd_717070 < baseStart_717070 := by decide
  rcases family_descends (prefixWord ++ tailWord_717070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717073 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 2, 7]
def baseStart_717073 : Nat := 118140960795 + 717073 * 2 ^ 59
def prefixEnd_717073 : Nat := 4983230072969 + 3 ^ 40 * 717073 * 2
def baseEnd_717073 : Nat := 122734371120526060763249

theorem tailTrace_717073 : CollatzResearch.WordTrace tailWord_717073 prefixEnd_717073 122734371120526060763249 := by
  unfold tailWord_717073
  simp only [CollatzResearch.WordTrace]
  refine ⟨26153800931174462163467873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17435867287449641442311915 26153800931174462163467873)
  ·
    refine ⟨19615350698380846622600905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26153800931174462163467873 19615350698380846622600905)
    ·
      refine ⟨14711513023785634966950679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19615350698380846622600905 14711513023785634966950679)
      ·
        refine ⟨22067269535678452450426019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14711513023785634966950679 22067269535678452450426019)
        ·
          refine ⟨33100904303517678675639029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22067269535678452450426019 33100904303517678675639029)
          ·
            refine ⟨3103209778454782375841159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33100904303517678675639029 3103209778454782375841159)
            ·
              refine ⟨4654814667682173563761739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3103209778454782375841159 4654814667682173563761739)
              ·
                refine ⟨6982222001523260345642609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4654814667682173563761739 6982222001523260345642609)
                ·
                  refine ⟨5236666501142445259231957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6982222001523260345642609 5236666501142445259231957)
                  ·
                    refine ⟨122734371120526060763249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5236666501142445259231957 122734371120526060763249)
                    ·
                      rfl

theorem cell23_717073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_717073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717073 prefixEnd_717073 := by exact prefixLift 717073
  have htrace : WordTrace (prefixWord ++ tailWord_717073) baseStart_717073 baseEnd_717073 := by
    simpa [prefixWord, tailWord_717073, baseEnd_717073] using wordTrace_append hprefix tailTrace_717073
  have hstable : (prefixWord ++ tailWord_717073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717073).length < 2 ^ (prefixWord ++ tailWord_717073).sum := by decide
  have hdescent : baseEnd_717073 < baseStart_717073 := by decide
  rcases family_descends (prefixWord ++ tailWord_717073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717087 : List Nat := [1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 3]
def baseStart_717087 : Nat := 118140960795 + 717087 * 2 ^ 59
def prefixEnd_717087 : Nat := 4983230072969 + 3 ^ 40 * 717087 * 2
def baseEnd_717087 : Nat := 368210302090741127514683

theorem tailTrace_717087 : CollatzResearch.WordTrace tailWord_717087 prefixEnd_717087 368210302090741127514683 := by
  unfold tailWord_717087
  simp only [CollatzResearch.WordTrace]
  refine ⟨26154311553123742554477515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17436207702082495036318343 26154311553123742554477515)
  ·
    refine ⟨39231467329685613831716273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26154311553123742554477515 39231467329685613831716273)
    ·
      refine ⟨29423600497264210373787205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39231467329685613831716273 29423600497264210373787205)
      ·
        refine ⟨5516925093237039445085101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29423600497264210373787205 5516925093237039445085101)
        ·
          refine ⟨2068846909963889791906913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5516925093237039445085101 2068846909963889791906913)
          ·
            refine ⟨1551635182472917343930185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2068846909963889791906913 1551635182472917343930185)
            ·
              refine ⟨1163726386854688007947639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1551635182472917343930185 1163726386854688007947639)
              ·
                refine ⟨1745589580282032011921459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163726386854688007947639 1745589580282032011921459)
                ·
                  refine ⟨2618384370423048017882189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1745589580282032011921459 2618384370423048017882189)
                  ·
                    refine ⟨981894138908643006705821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2618384370423048017882189 981894138908643006705821)
                    ·
                      refine ⟨368210302090741127514683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 981894138908643006705821 368210302090741127514683)
                      ·
                        rfl

theorem cell23_717087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_717087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717087 prefixEnd_717087 := by exact prefixLift 717087
  have htrace : WordTrace (prefixWord ++ tailWord_717087) baseStart_717087 baseEnd_717087 := by
    simpa [prefixWord, tailWord_717087, baseEnd_717087] using wordTrace_append hprefix tailTrace_717087
  have hstable : (prefixWord ++ tailWord_717087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717087).length < 2 ^ (prefixWord ++ tailWord_717087).sum := by decide
  have hdescent : baseEnd_717087 < baseStart_717087 := by decide
  rcases family_descends (prefixWord ++ tailWord_717087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717114 : List Nat := [3, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2]
def baseStart_717114 : Nat := 118140960795 + 717114 * 2 ^ 59
def prefixEnd_717114 : Nat := 4983230072969 + 3 ^ 40 * 717114 * 2
def baseEnd_717114 : Nat := 368224166068412521877059

theorem tailTrace_717114 : CollatzResearch.WordTrace tailWord_717114 prefixEnd_717114 368224166068412521877059 := by
  unfold tailWord_717114
  simp only [CollatzResearch.WordTrace]
  refine ⟨6538824081006481541427599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17436864216017284110473597 6538824081006481541427599)
  ·
    refine ⟨9808236121509722312141399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6538824081006481541427599 9808236121509722312141399)
    ·
      refine ⟨14712354182264583468212099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9808236121509722312141399 14712354182264583468212099)
      ·
        refine ⟨22068531273396875202318149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14712354182264583468212099 22068531273396875202318149)
        ·
          refine ⟨4137849613761914100434653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22068531273396875202318149 4137849613761914100434653)
          ·
            refine ⟨1551693605160717787662995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4137849613761914100434653 1551693605160717787662995)
            ·
              refine ⟨2327540407741076681494493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1551693605160717787662995 2327540407741076681494493)
              ·
                refine ⟨872827652902903755560435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2327540407741076681494493 872827652902903755560435)
                ·
                  refine ⟨1309241479354355633340653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 872827652902903755560435 1309241479354355633340653)
                  ·
                    refine ⟨490965554757883362502745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1309241479354355633340653 490965554757883362502745)
                    ·
                      refine ⟨368224166068412521877059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 490965554757883362502745 368224166068412521877059)
                      ·
                        rfl

theorem cell23_717114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2].length) (baseStart_717114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717114 prefixEnd_717114 := by exact prefixLift 717114
  have htrace : WordTrace (prefixWord ++ tailWord_717114) baseStart_717114 baseEnd_717114 := by
    simpa [prefixWord, tailWord_717114, baseEnd_717114] using wordTrace_append hprefix tailTrace_717114
  have hstable : (prefixWord ++ tailWord_717114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717114).length < 2 ^ (prefixWord ++ tailWord_717114).sum := by decide
  have hdescent : baseEnd_717114 < baseStart_717114 := by decide
  rcases family_descends (prefixWord ++ tailWord_717114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717148 : List Nat := [2, 2, 4, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_717148 : Nat := 118140960795 + 717148 * 2 ^ 59
def prefixEnd_717148 : Nat := 4983230072969 + 3 ^ 40 * 717148 * 2
def baseEnd_717148 : Nat := 368241624410665388851903

theorem tailTrace_717148 : CollatzResearch.WordTrace tailWord_717148 prefixEnd_717148 368241624410665388851903 := by
  unfold tailWord_717148
  simp only [CollatzResearch.WordTrace]
  refine ⟨13078268202951374986224049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17437690937268499981632065 13078268202951374986224049)
  ·
    refine ⟨9808701152213531239668037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13078268202951374986224049 9808701152213531239668037)
    ·
      refine ⟨1839131466040037107437757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9808701152213531239668037 1839131466040037107437757)
      ·
        refine ⟨689674299765013915289159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1839131466040037107437757 689674299765013915289159)
        ·
          refine ⟨1034511449647520872933739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689674299765013915289159 1034511449647520872933739)
          ·
            refine ⟨1551767174471281309400609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034511449647520872933739 1551767174471281309400609)
            ·
              refine ⟨1163825380853460982050457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1551767174471281309400609 1163825380853460982050457)
              ·
                refine ⟨872869035640095736537843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1163825380853460982050457 872869035640095736537843)
                ·
                  refine ⟨1309303553460143604806765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 872869035640095736537843 1309303553460143604806765)
                  ·
                    refine ⟨490988832547553851802537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1309303553460143604806765 490988832547553851802537)
                    ·
                      refine ⟨368241624410665388851903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 490988832547553851802537 368241624410665388851903)
                      ·
                        rfl

theorem cell23_717148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_717148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717148 prefixEnd_717148 := by exact prefixLift 717148
  have htrace : WordTrace (prefixWord ++ tailWord_717148) baseStart_717148 baseEnd_717148 := by
    simpa [prefixWord, tailWord_717148, baseEnd_717148] using wordTrace_append hprefix tailTrace_717148
  have hstable : (prefixWord ++ tailWord_717148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717148).length < 2 ^ (prefixWord ++ tailWord_717148).sum := by decide
  have hdescent : baseEnd_717148 < baseStart_717148 := by decide
  rcases family_descends (prefixWord ++ tailWord_717148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717214 : List Nat := [4, 3, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_717214 : Nat := 118140960795 + 717214 * 2 ^ 59
def prefixEnd_717214 : Nat := 4983230072969 + 3 ^ 40 * 717214 * 2
def baseEnd_717214 : Nat := 122758504711287376875533

theorem tailTrace_717214 : CollatzResearch.WordTrace tailWord_717214 prefixEnd_717214 122758504711287376875533 := by
  unfold tailWord_717214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3269867952957955405543837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17439295749109095496233797 3269867952957955405543837)
  ·
    refine ⟨1226200482359233277078939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3269867952957955405543837 1226200482359233277078939)
    ·
      refine ⟨1839300723538849915618409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1226200482359233277078939 1839300723538849915618409)
      ·
        refine ⟨1379475542654137436713807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1839300723538849915618409 1379475542654137436713807)
        ·
          refine ⟨2069213313981206155070711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1379475542654137436713807 2069213313981206155070711)
          ·
            refine ⟨3103819970971809232606067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2069213313981206155070711 3103819970971809232606067)
            ·
              refine ⟨4655729956457713848909101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3103819970971809232606067 4655729956457713848909101)
              ·
                refine ⟨1745898733671642693340913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4655729956457713848909101 1745898733671642693340913)
                ·
                  refine ⟨1309424050253732020005685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1745898733671642693340913 1309424050253732020005685)
                  ·
                    refine ⟨122758504711287376875533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1309424050253732020005685 122758504711287376875533)
                    ·
                      rfl

theorem cell23_717214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_717214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717214 prefixEnd_717214 := by exact prefixLift 717214
  have htrace : WordTrace (prefixWord ++ tailWord_717214) baseStart_717214 baseEnd_717214 := by
    simpa [prefixWord, tailWord_717214, baseEnd_717214] using wordTrace_append hprefix tailTrace_717214
  have hstable : (prefixWord ++ tailWord_717214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717214).length < 2 ^ (prefixWord ++ tailWord_717214).sum := by decide
  have hdescent : baseEnd_717214 < baseStart_717214 := by decide
  rcases family_descends (prefixWord ++ tailWord_717214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717307 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 4, 6, 2]
def baseStart_717307 : Nat := 118140960795 + 717307 * 2 ^ 59
def prefixEnd_717307 : Nat := 4983230072969 + 3 ^ 40 * 717307 * 2
def baseEnd_717307 : Nat := 368323267834730266763671

theorem tailTrace_717307 : CollatzResearch.WordTrace tailWord_717307 prefixEnd_717307 368323267834730266763671 := by
  unfold tailWord_717307
  simp only [CollatzResearch.WordTrace]
  refine ⟨26162335612326720127486175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17441557074884480084990783 26162335612326720127486175)
  ·
    refine ⟨39243503418490080191229263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26162335612326720127486175 39243503418490080191229263)
    ·
      refine ⟨58865255127735120286843895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39243503418490080191229263 58865255127735120286843895)
      ·
        refine ⟨88297882691602680430265843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58865255127735120286843895 88297882691602680430265843)
        ·
          refine ⟨132446824037404020645398765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88297882691602680430265843 132446824037404020645398765)
          ·
            refine ⟨49667559014026507742024537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132446824037404020645398765 49667559014026507742024537)
            ·
              refine ⟨37250669260519880806518403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49667559014026507742024537 37250669260519880806518403)
              ·
                refine ⟨55876003890779821209777605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37250669260519880806518403 55876003890779821209777605)
                ·
                  refine ⟨10476750729521216476833301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55876003890779821209777605 10476750729521216476833301)
                  ·
                    refine ⟨491097690446307022351561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10476750729521216476833301 491097690446307022351561)
                    ·
                      refine ⟨368323267834730266763671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 491097690446307022351561 368323267834730266763671)
                      ·
                        rfl

theorem cell23_717307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 6, 2].length) (baseStart_717307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717307 prefixEnd_717307 := by exact prefixLift 717307
  have htrace : WordTrace (prefixWord ++ tailWord_717307) baseStart_717307 baseEnd_717307 := by
    simpa [prefixWord, tailWord_717307, baseEnd_717307] using wordTrace_append hprefix tailTrace_717307
  have hstable : (prefixWord ++ tailWord_717307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717307).length < 2 ^ (prefixWord ++ tailWord_717307).sum := by decide
  have hdescent : baseEnd_717307 < baseStart_717307 := by decide
  rcases family_descends (prefixWord ++ tailWord_717307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717317 : List Nat := [1, 3, 1, 1, 2, 2, 5, 1, 1, 6]
def baseStart_717317 : Nat := 118140960795 + 717317 * 2 ^ 59
def prefixEnd_717317 : Nat := 4983230072969 + 3 ^ 40 * 717317 * 2
def baseEnd_717317 : Nat := 122776134213758409212875

theorem tailTrace_717317 : CollatzResearch.WordTrace tailWord_717317 prefixEnd_717317 122776134213758409212875 := by
  unfold tailWord_717317
  simp only [CollatzResearch.WordTrace]
  refine ⟨26162700342290491835350205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17441800228193661223566803 26162700342290491835350205)
  ·
    refine ⟨9811012628358934438256327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26162700342290491835350205 9811012628358934438256327)
    ·
      refine ⟨14716518942538401657384491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9811012628358934438256327 14716518942538401657384491)
      ·
        refine ⟨22074778413807602486076737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14716518942538401657384491 22074778413807602486076737)
        ·
          refine ⟨16556083810355701864557553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22074778413807602486076737 16556083810355701864557553)
          ·
            refine ⟨12417062857766776398418165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16556083810355701864557553 12417062857766776398418165)
            ·
              refine ⟨1164099642915635287351703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12417062857766776398418165 1164099642915635287351703)
              ·
                refine ⟨1746149464373452931027555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1164099642915635287351703 1746149464373452931027555)
                ·
                  refine ⟨2619224196560179396541333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746149464373452931027555 2619224196560179396541333)
                  ·
                    refine ⟨122776134213758409212875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2619224196560179396541333 122776134213758409212875)
                    ·
                      rfl

theorem cell23_717317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_717317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717317 prefixEnd_717317 := by exact prefixLift 717317
  have htrace : WordTrace (prefixWord ++ tailWord_717317) baseStart_717317 baseEnd_717317 := by
    simpa [prefixWord, tailWord_717317, baseEnd_717317] using wordTrace_append hprefix tailTrace_717317
  have hstable : (prefixWord ++ tailWord_717317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717317).length < 2 ^ (prefixWord ++ tailWord_717317).sum := by decide
  have hdescent : baseEnd_717317 < baseStart_717317 := by decide
  rcases family_descends (prefixWord ++ tailWord_717317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717324 : List Nat := [2, 2, 1, 2, 4, 1, 1, 4, 1, 1, 4]
def baseStart_717324 : Nat := 118140960795 + 717324 * 2 ^ 59
def prefixEnd_717324 : Nat := 4983230072969 + 3 ^ 40 * 717324 * 2
def baseEnd_717324 : Nat := 368331997005856700251093

theorem tailTrace_717324 : CollatzResearch.WordTrace tailWord_717324 prefixEnd_717324 368331997005856700251093 := by
  unfold tailWord_717324
  simp only [CollatzResearch.WordTrace]
  refine ⟨13081477826632566015427513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17441970435510088020570017 13081477826632566015427513)
  ·
    refine ⟨9811108369974424511570635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13081477826632566015427513 9811108369974424511570635)
    ·
      refine ⟨14716662554961636767355953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9811108369974424511570635 14716662554961636767355953)
      ·
        refine ⟨11037496916221227575516965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14716662554961636767355953 11037496916221227575516965)
        ·
          refine ⟨2069530671791480170409431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11037496916221227575516965 2069530671791480170409431)
          ·
            refine ⟨3104296007687220255614147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2069530671791480170409431 3104296007687220255614147)
            ·
              refine ⟨4656444011530830383421221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3104296007687220255614147 4656444011530830383421221)
              ·
                refine ⟨873083252162030696891479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4656444011530830383421221 873083252162030696891479)
                ·
                  refine ⟨1309624878243046045337219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 873083252162030696891479 1309624878243046045337219)
                  ·
                    refine ⟨1964437317364569068005829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1309624878243046045337219 1964437317364569068005829)
                    ·
                      refine ⟨368331997005856700251093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1964437317364569068005829 368331997005856700251093)
                      ·
                        rfl

theorem cell23_717324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_717324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717324 prefixEnd_717324 := by exact prefixLift 717324
  have htrace : WordTrace (prefixWord ++ tailWord_717324) baseStart_717324 baseEnd_717324 := by
    simpa [prefixWord, tailWord_717324, baseEnd_717324] using wordTrace_append hprefix tailTrace_717324
  have hstable : (prefixWord ++ tailWord_717324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717324).length < 2 ^ (prefixWord ++ tailWord_717324).sum := by decide
  have hdescent : baseEnd_717324 < baseStart_717324 := by decide
  rcases family_descends (prefixWord ++ tailWord_717324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717347 : List Nat := [1, 1, 1, 4, 4, 3, 9]
def baseStart_717347 : Nat := 118140960795 + 717347 * 2 ^ 59
def prefixEnd_717347 : Nat := 4983230072969 + 3 ^ 40 * 717347 * 2
def baseEnd_717347 : Nat := 4547454408159384077327

theorem tailTrace_717347 : CollatzResearch.WordTrace tailWord_717347 prefixEnd_717347 4547454408159384077327 := by
  unfold tailWord_717347
  simp only [CollatzResearch.WordTrace]
  refine ⟨26163794532181806958942295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17442529688121204639294863 26163794532181806958942295)
  ·
    refine ⟨39245691798272710438413443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26163794532181806958942295 39245691798272710438413443)
    ·
      refine ⟨58868537697409065657620165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39245691798272710438413443 58868537697409065657620165)
      ·
        refine ⟨11037850818264199810803781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58868537697409065657620165 11037850818264199810803781)
        ·
          refine ⟨2069597028424537464525709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11037850818264199810803781 2069597028424537464525709)
          ·
            refine ⟨776098885659201549197141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2069597028424537464525709 776098885659201549197141)
            ·
              refine ⟨4547454408159384077327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 776098885659201549197141 4547454408159384077327)
              ·
                rfl

theorem cell23_717347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 9].length) (baseStart_717347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717347 prefixEnd_717347 := by exact prefixLift 717347
  have htrace : WordTrace (prefixWord ++ tailWord_717347) baseStart_717347 baseEnd_717347 := by
    simpa [prefixWord, tailWord_717347, baseEnd_717347] using wordTrace_append hprefix tailTrace_717347
  have hstable : (prefixWord ++ tailWord_717347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717347).length < 2 ^ (prefixWord ++ tailWord_717347).sum := by decide
  have hdescent : baseEnd_717347 < baseStart_717347 := by decide
  rcases family_descends (prefixWord ++ tailWord_717347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717424 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 2, 6]
def baseStart_717424 : Nat := 118140960795 + 717424 * 2 ^ 59
def prefixEnd_717424 : Nat := 4983230072969 + 3 ^ 40 * 717424 * 2
def baseEnd_717424 : Nat := 122794448357102103000211

theorem tailTrace_717424 : CollatzResearch.WordTrace tailWord_717424 prefixEnd_717424 122794448357102103000211 := by
  unfold tailWord_717424
  simp only [CollatzResearch.WordTrace]
  refine ⟨13083301476451424554747663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17444401968601899406330217 13083301476451424554747663)
  ·
    refine ⟨19624952214677136832121495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13083301476451424554747663 19624952214677136832121495)
    ·
      refine ⟨29437428322015705248182243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19624952214677136832121495 29437428322015705248182243)
      ·
        refine ⟨44156142483023557872273365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29437428322015705248182243 44156142483023557872273365)
        ·
          refine ⟨1034909589445864637631407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 44156142483023557872273365 1034909589445864637631407)
          ·
            refine ⟨1552364384168796956447111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034909589445864637631407 1552364384168796956447111)
            ·
              refine ⟨2328546576253195434670667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1552364384168796956447111 2328546576253195434670667)
              ·
                refine ⟨3492819864379793152006001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2328546576253195434670667 3492819864379793152006001)
                ·
                  refine ⟨2619614898284844864004501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3492819864379793152006001 2619614898284844864004501)
                  ·
                    refine ⟨122794448357102103000211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2619614898284844864004501 122794448357102103000211)
                    ·
                      rfl

theorem cell23_717424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 2, 6].length) (baseStart_717424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717424 prefixEnd_717424 := by exact prefixLift 717424
  have htrace : WordTrace (prefixWord ++ tailWord_717424) baseStart_717424 baseEnd_717424 := by
    simpa [prefixWord, tailWord_717424, baseEnd_717424] using wordTrace_append hprefix tailTrace_717424
  have hstable : (prefixWord ++ tailWord_717424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717424).length < 2 ^ (prefixWord ++ tailWord_717424).sum := by decide
  have hdescent : baseEnd_717424 < baseStart_717424 := by decide
  rcases family_descends (prefixWord ++ tailWord_717424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717464 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 4, 3, 3]
def baseStart_717464 : Nat := 118140960795 + 717464 * 2 ^ 59
def prefixEnd_717464 : Nat := 4983230072969 + 3 ^ 40 * 717464 * 2
def baseEnd_717464 : Nat := 368403884297486152500449

theorem tailTrace_717464 : CollatzResearch.WordTrace tailWord_717464 prefixEnd_717464 368403884297486152500449 := by
  unfold tailWord_717464
  simp only [CollatzResearch.WordTrace]
  refine ⟨13084030936378967970475723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17445374581838623960634297 13084030936378967970475723)
  ·
    refine ⟨19626046404568451955713585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13084030936378967970475723 19626046404568451955713585)
    ·
      refine ⟨14719534803426338966785189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19626046404568451955713585 14719534803426338966785189)
      ·
        refine ⟨2759912775642438556272223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14719534803426338966785189 2759912775642438556272223)
        ·
          refine ⟨4139869163463657834408335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2759912775642438556272223 4139869163463657834408335)
          ·
            refine ⟨6209803745195486751612503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4139869163463657834408335 6209803745195486751612503)
            ·
              refine ⟨9314705617793230127418755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6209803745195486751612503 9314705617793230127418755)
              ·
                refine ⟨13972058426689845191128133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9314705617793230127418755 13972058426689845191128133)
                ·
                  refine ⟨2619760955004345973336525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13972058426689845191128133 2619760955004345973336525)
                  ·
                    refine ⟨982410358126629740001197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2619760955004345973336525 982410358126629740001197)
                    ·
                      refine ⟨368403884297486152500449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 982410358126629740001197 368403884297486152500449)
                      ·
                        rfl

theorem cell23_717464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_717464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717464 prefixEnd_717464 := by exact prefixLift 717464
  have htrace : WordTrace (prefixWord ++ tailWord_717464) baseStart_717464 baseEnd_717464 := by
    simpa [prefixWord, tailWord_717464, baseEnd_717464] using wordTrace_append hprefix tailTrace_717464
  have hstable : (prefixWord ++ tailWord_717464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717464).length < 2 ^ (prefixWord ++ tailWord_717464).sum := by decide
  have hdescent : baseEnd_717464 < baseStart_717464 := by decide
  rcases family_descends (prefixWord ++ tailWord_717464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717467 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 8, 5]
def baseStart_717467 : Nat := 118140960795 + 717467 * 2 ^ 59
def prefixEnd_717467 : Nat := 4983230072969 + 3 ^ 40 * 717467 * 2
def baseEnd_717467 : Nat := 122801808246483213587645

theorem tailTrace_717467 : CollatzResearch.WordTrace tailWord_717467 prefixEnd_717467 122801808246483213587645 := by
  unfold tailWord_717467
  simp only [CollatzResearch.WordTrace]
  refine ⟨26168171291747067453310655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17445447527831378302207103 26168171291747067453310655)
  ·
    refine ⟨39252256937620601179965983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26168171291747067453310655 39252256937620601179965983)
    ·
      refine ⟨58878385406430901769948975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39252256937620601179965983 58878385406430901769948975)
      ·
        refine ⟨88317578109646352654923463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58878385406430901769948975 88317578109646352654923463)
        ·
          refine ⟨132476367164469528982385195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88317578109646352654923463 132476367164469528982385195)
          ·
            refine ⟨198714550746704293473577793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132476367164469528982385195 198714550746704293473577793)
            ·
              refine ⟨149035913060028220105183345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198714550746704293473577793 149035913060028220105183345)
              ·
                refine ⟨111776934795021165078887509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149035913060028220105183345 111776934795021165078887509)
                ·
                  refine ⟨1309885954629154278268213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 111776934795021165078887509 1309885954629154278268213)
                  ·
                    refine ⟨122801808246483213587645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1309885954629154278268213 122801808246483213587645)
                    ·
                      rfl

theorem cell23_717467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 5].length) (baseStart_717467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717467 prefixEnd_717467 := by exact prefixLift 717467
  have htrace : WordTrace (prefixWord ++ tailWord_717467) baseStart_717467 baseEnd_717467 := by
    simpa [prefixWord, tailWord_717467, baseEnd_717467] using wordTrace_append hprefix tailTrace_717467
  have hstable : (prefixWord ++ tailWord_717467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717467).length < 2 ^ (prefixWord ++ tailWord_717467).sum := by decide
  have hdescent : baseEnd_717467 < baseStart_717467 := by decide
  rcases family_descends (prefixWord ++ tailWord_717467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717477 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 1, 1, 7]
def baseStart_717477 : Nat := 118140960795 + 717477 * 2 ^ 59
def prefixEnd_717477 : Nat := 4983230072969 + 3 ^ 40 * 717477 * 2
def baseEnd_717477 : Nat := 368410559545994601637889

theorem tailTrace_717477 : CollatzResearch.WordTrace tailWord_717477 prefixEnd_717477 368410559545994601637889 := by
  unfold tailWord_717477
  simp only [CollatzResearch.WordTrace]
  refine ⟨26168536021710839161174685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17445690681140559440783123 26168536021710839161174685)
  ·
    refine ⟨9813201008141564685440507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26168536021710839161174685 9813201008141564685440507)
    ·
      refine ⟨14719801512212347028160761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9813201008141564685440507 14719801512212347028160761)
      ·
        refine ⟨11039851134159260271120571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14719801512212347028160761 11039851134159260271120571)
        ·
          refine ⟨16559776701238890406680857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11039851134159260271120571 16559776701238890406680857)
          ·
            refine ⟨12419832525929167805010643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16559776701238890406680857 12419832525929167805010643)
            ·
              refine ⟨18629748788893751707515965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12419832525929167805010643 18629748788893751707515965)
              ·
                refine ⟨6986155795835156890318487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18629748788893751707515965 6986155795835156890318487)
                ·
                  refine ⟨10479233693752735335477731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6986155795835156890318487 10479233693752735335477731)
                  ·
                    refine ⟨15718850540629103003216597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10479233693752735335477731 15718850540629103003216597)
                    ·
                      refine ⟨368410559545994601637889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15718850540629103003216597 368410559545994601637889)
                      ·
                        rfl

theorem cell23_717477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_717477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717477 prefixEnd_717477 := by exact prefixLift 717477
  have htrace : WordTrace (prefixWord ++ tailWord_717477) baseStart_717477 baseEnd_717477 := by
    simpa [prefixWord, tailWord_717477, baseEnd_717477] using wordTrace_append hprefix tailTrace_717477
  have hstable : (prefixWord ++ tailWord_717477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717477).length < 2 ^ (prefixWord ++ tailWord_717477).sum := by decide
  have hdescent : baseEnd_717477 < baseStart_717477 := by decide
  rcases family_descends (prefixWord ++ tailWord_717477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717482 : List Nat := [3, 1, 5, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_717482 : Nat := 118140960795 + 717482 * 2 ^ 59
def prefixEnd_717482 : Nat := 4983230072969 + 3 ^ 40 * 717482 * 2
def baseEnd_717482 : Nat := 368413126949267082075367

theorem tailTrace_717482 : CollatzResearch.WordTrace tailWord_717482 prefixEnd_717482 368413126949267082075367 := by
  unfold tailWord_717482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6542179596673181253776675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17445812257795150010071133 6542179596673181253776675)
  ·
    refine ⟨9813269395009771880665013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6542179596673181253776675 9813269395009771880665013)
    ·
      refine ⟨919994005782166113812345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9813269395009771880665013 919994005782166113812345)
      ·
        refine ⟨689995504336624585359259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 919994005782166113812345 689995504336624585359259)
        ·
          refine ⟨1034993256504936878038889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689995504336624585359259 1034993256504936878038889)
          ·
            refine ⟨776244942378702658529167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1034993256504936878038889 776244942378702658529167)
            ·
              refine ⟨1164367413568053987793751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 776244942378702658529167 1164367413568053987793751)
              ·
                refine ⟨1746551120352080981690627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1164367413568053987793751 1746551120352080981690627)
                ·
                  refine ⟨2619826680528121472535941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746551120352080981690627 2619826680528121472535941)
                  ·
                    refine ⟨491217502599022776100489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2619826680528121472535941 491217502599022776100489)
                    ·
                      refine ⟨368413126949267082075367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 491217502599022776100489 368413126949267082075367)
                      ·
                        rfl

theorem cell23_717482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_717482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717482 prefixEnd_717482 := by exact prefixLift 717482
  have htrace : WordTrace (prefixWord ++ tailWord_717482) baseStart_717482 baseEnd_717482 := by
    simpa [prefixWord, tailWord_717482, baseEnd_717482] using wordTrace_append hprefix tailTrace_717482
  have hstable : (prefixWord ++ tailWord_717482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717482).length < 2 ^ (prefixWord ++ tailWord_717482).sum := by decide
  have hdescent : baseEnd_717482 < baseStart_717482 := by decide
  rcases family_descends (prefixWord ++ tailWord_717482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717497 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 1, 10]
def baseStart_717497 : Nat := 118140960795 + 717497 * 2 ^ 59
def prefixEnd_717497 : Nat := 4983230072969 + 3 ^ 40 * 717497 * 2
def baseEnd_717497 : Nat := 122806943053028174462599

theorem tailTrace_717497 : CollatzResearch.WordTrace tailWord_717497 prefixEnd_717497 122806943053028174462599 := by
  unfold tailWord_717497
  simp only [CollatzResearch.WordTrace]
  refine ⟨26169265481638382576902745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17446176987758921717935163 26169265481638382576902745)
  ·
    refine ⟨19626949111228786932677059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26169265481638382576902745 19626949111228786932677059)
    ·
      refine ⟨29440423666843180399015589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19626949111228786932677059 29440423666843180399015589)
      ·
        refine ⟨5520079437533096324815423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29440423666843180399015589 5520079437533096324815423)
        ·
          refine ⟨8280119156299644487223135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5520079437533096324815423 8280119156299644487223135)
          ·
            refine ⟨12420178734449466730834703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8280119156299644487223135 12420178734449466730834703)
            ·
              refine ⟨18630268101674200096252055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12420178734449466730834703 18630268101674200096252055)
              ·
                refine ⟨27945402152511300144378083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18630268101674200096252055 27945402152511300144378083)
                ·
                  refine ⟨41918103228766950216567125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27945402152511300144378083 41918103228766950216567125)
                  ·
                    refine ⟨122806943053028174462599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 41918103228766950216567125 122806943053028174462599)
                    ·
                      rfl

theorem cell23_717497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 10].length) (baseStart_717497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717497 prefixEnd_717497 := by exact prefixLift 717497
  have htrace : WordTrace (prefixWord ++ tailWord_717497) baseStart_717497 baseEnd_717497 := by
    simpa [prefixWord, tailWord_717497, baseEnd_717497] using wordTrace_append hprefix tailTrace_717497
  have hstable : (prefixWord ++ tailWord_717497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717497).length < 2 ^ (prefixWord ++ tailWord_717497).sum := by decide
  have hdescent : baseEnd_717497 < baseStart_717497 := by decide
  rcases family_descends (prefixWord ++ tailWord_717497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717504 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 4]
def baseStart_717504 : Nat := 118140960795 + 717504 * 2 ^ 59
def prefixEnd_717504 : Nat := 4983230072969 + 3 ^ 40 * 717504 * 2
def baseEnd_717504 : Nat := 368424423523665996000265

theorem tailTrace_717504 : CollatzResearch.WordTrace tailWord_717504 prefixEnd_717504 368424423523665996000265 := by
  unfold tailWord_717504
  simp only [CollatzResearch.WordTrace]
  refine ⟨13084760396306511386203783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17446347195075348514938377 13084760396306511386203783)
  ·
    refine ⟨19627140594459767079305675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13084760396306511386203783 19627140594459767079305675)
    ·
      refine ⟨29440710891689650618958513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19627140594459767079305675 29440710891689650618958513)
      ·
        refine ⟨22080533168767237964218885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29440710891689650618958513 22080533168767237964218885)
        ·
          refine ⟨4140099969143857118291041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22080533168767237964218885 4140099969143857118291041)
          ·
            refine ⟨3105074976857892838718281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4140099969143857118291041 3105074976857892838718281)
            ·
              refine ⟨2328806232643419629038711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3105074976857892838718281 2328806232643419629038711)
              ·
                refine ⟨3493209348965129443558067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2328806232643419629038711 3493209348965129443558067)
                ·
                  refine ⟨5239814023447694165337101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3493209348965129443558067 5239814023447694165337101)
                  ·
                    refine ⟨1964930258792885312001413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5239814023447694165337101 1964930258792885312001413)
                    ·
                      refine ⟨368424423523665996000265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1964930258792885312001413 368424423523665996000265)
                      ·
                        rfl

theorem cell23_717504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_717504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717504 prefixEnd_717504 := by exact prefixLift 717504
  have htrace : WordTrace (prefixWord ++ tailWord_717504) baseStart_717504 baseEnd_717504 := by
    simpa [prefixWord, tailWord_717504, baseEnd_717504] using wordTrace_append hprefix tailTrace_717504
  have hstable : (prefixWord ++ tailWord_717504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717504).length < 2 ^ (prefixWord ++ tailWord_717504).sum := by decide
  have hdescent : baseEnd_717504 < baseStart_717504 := by decide
  rcases family_descends (prefixWord ++ tailWord_717504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717558 : List Nat := [5, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_717558 : Nat := 118140960795 + 717558 * 2 ^ 59
def prefixEnd_717558 : Nat := 4983230072969 + 3 ^ 40 * 717558 * 2
def baseEnd_717558 : Nat := 368452151479008784725017

theorem tailTrace_717558 : CollatzResearch.WordTrace tailWord_717558 prefixEnd_717558 368452151479008784725017 := by
  unfold tailWord_717558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1635718145901086874679583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17447660222944926663248885 1635718145901086874679583)
  ·
    refine ⟨2453577218851630312019375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1635718145901086874679583 2453577218851630312019375)
    ·
      refine ⟨3680365828277445468029063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2453577218851630312019375 3680365828277445468029063)
      ·
        refine ⟨5520548742416168202043595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3680365828277445468029063 5520548742416168202043595)
        ·
          refine ⟨8280823113624252303065393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5520548742416168202043595 8280823113624252303065393)
          ·
            refine ⟨6210617335218189227299045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8280823113624252303065393 6210617335218189227299045)
            ·
              refine ⟨1164490750353410480118571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6210617335218189227299045 1164490750353410480118571)
              ·
                refine ⟨1746736125530115720177857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1164490750353410480118571 1746736125530115720177857)
                ·
                  refine ⟨1310052094147586790133393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1746736125530115720177857 1310052094147586790133393)
                  ·
                    refine ⟨982539070610690092600045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1310052094147586790133393 982539070610690092600045)
                    ·
                      refine ⟨368452151479008784725017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 982539070610690092600045 368452151479008784725017)
                      ·
                        rfl

theorem cell23_717558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_717558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717558 prefixEnd_717558 := by exact prefixLift 717558
  have htrace : WordTrace (prefixWord ++ tailWord_717558) baseStart_717558 baseEnd_717558 := by
    simpa [prefixWord, tailWord_717558, baseEnd_717558] using wordTrace_append hprefix tailTrace_717558
  have hstable : (prefixWord ++ tailWord_717558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717558).length < 2 ^ (prefixWord ++ tailWord_717558).sum := by decide
  have hdescent : baseEnd_717558 < baseStart_717558 := by decide
  rcases family_descends (prefixWord ++ tailWord_717558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717621 : List Nat := [1, 3, 3, 1, 3, 1, 2, 2, 1, 6]
def baseStart_717621 : Nat := 118140960795 + 717621 * 2 ^ 59
def prefixEnd_717621 : Nat := 4983230072969 + 3 ^ 40 * 717621 * 2
def baseEnd_717621 : Nat := 122828166920080679412409

theorem tailTrace_717621 : CollatzResearch.WordTrace tailWord_717621 prefixEnd_717621 122828166920080679412409 := by
  unfold tailWord_717621
  simp only [CollatzResearch.WordTrace]
  refine ⟨26173788133189151754416717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17449192088792767836277811 26173788133189151754416717)
  ·
    refine ⟨9815170549945931907906269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26173788133189151754416717 9815170549945931907906269)
    ·
      refine ⟨3680688956229724465464851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9815170549945931907906269 3680688956229724465464851)
      ·
        refine ⟨5521033434344586698197277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3680688956229724465464851 5521033434344586698197277)
        ·
          refine ⟨2070387537879220011823979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5521033434344586698197277 2070387537879220011823979)
          ·
            refine ⟨3105581306818830017735969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2070387537879220011823979 3105581306818830017735969)
            ·
              refine ⟨2329185980114122513301977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3105581306818830017735969 2329185980114122513301977)
              ·
                refine ⟨1746889485085591884976483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2329185980114122513301977 1746889485085591884976483)
                ·
                  refine ⟨2620334227628387827464725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746889485085591884976483 2620334227628387827464725)
                  ·
                    refine ⟨122828166920080679412409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2620334227628387827464725 122828166920080679412409)
                    ·
                      rfl

theorem cell23_717621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_717621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717621 prefixEnd_717621 := by exact prefixLift 717621
  have htrace : WordTrace (prefixWord ++ tailWord_717621) baseStart_717621 baseEnd_717621 := by
    simpa [prefixWord, tailWord_717621, baseEnd_717621] using wordTrace_append hprefix tailTrace_717621
  have hstable : (prefixWord ++ tailWord_717621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717621).length < 2 ^ (prefixWord ++ tailWord_717621).sum := by decide
  have hdescent : baseEnd_717621 < baseStart_717621 := by decide
  rcases family_descends (prefixWord ++ tailWord_717621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717628 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 7, 2, 2]
def baseStart_717628 : Nat := 118140960795 + 717628 * 2 ^ 59
def prefixEnd_717628 : Nat := 4983230072969 + 3 ^ 40 * 717628 * 2
def baseEnd_717628 : Nat := 368488095124823510849695

theorem tailTrace_717628 : CollatzResearch.WordTrace tailWord_717628 prefixEnd_717628 368488095124823510849695 := by
  unfold tailWord_717628
  simp only [CollatzResearch.WordTrace]
  refine ⟨13087021722081895974960769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17449362296109194633281025 13087021722081895974960769)
  ·
    refine ⟨9815266291561421981220577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13087021722081895974960769 9815266291561421981220577)
    ·
      refine ⟨7361449718671066485915433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9815266291561421981220577 7361449718671066485915433)
      ·
        refine ⟨5521087289003299864436575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7361449718671066485915433 5521087289003299864436575)
        ·
          refine ⟨8281630933504949796654863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5521087289003299864436575 8281630933504949796654863)
          ·
            refine ⟨12422446400257424694982295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8281630933504949796654863 12422446400257424694982295)
            ·
              refine ⟨18633669600386137042473443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12422446400257424694982295 18633669600386137042473443)
              ·
                refine ⟨27950504400579205563710165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18633669600386137042473443 27950504400579205563710165)
                ·
                  refine ⟨655089946888575130399457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 27950504400579205563710165 655089946888575130399457)
                  ·
                    refine ⟨491317460166431347799593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 655089946888575130399457 491317460166431347799593)
                    ·
                      refine ⟨368488095124823510849695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 491317460166431347799593 368488095124823510849695)
                      ·
                        rfl

theorem cell23_717628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_717628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717628 prefixEnd_717628 := by exact prefixLift 717628
  have htrace : WordTrace (prefixWord ++ tailWord_717628) baseStart_717628 baseEnd_717628 := by
    simpa [prefixWord, tailWord_717628, baseEnd_717628] using wordTrace_append hprefix tailTrace_717628
  have hstable : (prefixWord ++ tailWord_717628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717628).length < 2 ^ (prefixWord ++ tailWord_717628).sum := by decide
  have hdescent : baseEnd_717628 < baseStart_717628 := by decide
  rcases family_descends (prefixWord ++ tailWord_717628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717655 : List Nat := [1, 1, 3, 2, 4, 2, 3, 1, 2, 4]
def baseStart_717655 : Nat := 118140960795 + 717655 * 2 ^ 59
def prefixEnd_717655 : Nat := 4983230072969 + 3 ^ 40 * 717655 * 2
def baseEnd_717655 : Nat := 122833986367498301737357

theorem tailTrace_717655 : CollatzResearch.WordTrace tailWord_717655 prefixEnd_717655 122833986367498301737357 := by
  unfold tailWord_717655
  simp only [CollatzResearch.WordTrace]
  refine ⟨26175028215065975561154419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17450018810043983707436279 26175028215065975561154419)
  ·
    refine ⟨39262542322598963341731629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26175028215065975561154419 39262542322598963341731629)
    ·
      refine ⟨14723453370974611253149361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39262542322598963341731629 14723453370974611253149361)
      ·
        refine ⟨11042590028230958439862021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14723453370974611253149361 11042590028230958439862021)
        ·
          refine ⟨2070485630293304707474129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11042590028230958439862021 2070485630293304707474129)
          ·
            refine ⟨1552864222719978530605597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2070485630293304707474129 1552864222719978530605597)
            ·
              refine ⟨582324083519991948977099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1552864222719978530605597 582324083519991948977099)
              ·
                refine ⟨873486125279987923465649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582324083519991948977099 873486125279987923465649)
                ·
                  refine ⟨655114593959990942599237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 873486125279987923465649 655114593959990942599237)
                  ·
                    refine ⟨122833986367498301737357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 655114593959990942599237 122833986367498301737357)
                    ·
                      rfl

theorem cell23_717655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 2, 4].length) (baseStart_717655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717655 prefixEnd_717655 := by exact prefixLift 717655
  have htrace : WordTrace (prefixWord ++ tailWord_717655) baseStart_717655 baseEnd_717655 := by
    simpa [prefixWord, tailWord_717655, baseEnd_717655] using wordTrace_append hprefix tailTrace_717655
  have hstable : (prefixWord ++ tailWord_717655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717655).length < 2 ^ (prefixWord ++ tailWord_717655).sum := by decide
  have hdescent : baseEnd_717655 < baseStart_717655 := by decide
  rcases family_descends (prefixWord ++ tailWord_717655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717658 : List Nat := [3, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4]
def baseStart_717658 : Nat := 118140960795 + 717658 * 2 ^ 59
def prefixEnd_717658 : Nat := 4983230072969 + 3 ^ 40 * 717658 * 2
def baseEnd_717658 : Nat := 368503499544458393474557

theorem tailTrace_717658 : CollatzResearch.WordTrace tailWord_717658 prefixEnd_717658 368503499544458393474557 := by
  unfold tailWord_717658
  simp only [CollatzResearch.WordTrace]
  refine ⟨6543784408513776768378407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17450091756036738049009085 6543784408513776768378407)
  ·
    refine ⟨9815676612770665152567611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6543784408513776768378407 9815676612770665152567611)
    ·
      refine ⟨14723514919155997728851417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9815676612770665152567611 14723514919155997728851417)
      ·
        refine ⟨11042636189366998296638563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14723514919155997728851417 11042636189366998296638563)
        ·
          refine ⟨16563954284050497444957845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11042636189366998296638563 16563954284050497444957845)
          ·
            refine ⟨776435357064867067732399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16563954284050497444957845 776435357064867067732399)
            ·
              refine ⟨1164653035597300601598599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 776435357064867067732399 1164653035597300601598599)
              ·
                refine ⟨1746979553395950902397899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1164653035597300601598599 1746979553395950902397899)
                ·
                  refine ⟨2620469330093926353596849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746979553395950902397899 2620469330093926353596849)
                  ·
                    refine ⟨1965351997570444765197637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2620469330093926353596849 1965351997570444765197637)
                    ·
                      refine ⟨368503499544458393474557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1965351997570444765197637 368503499544458393474557)
                      ·
                        rfl

theorem cell23_717658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_717658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717658 prefixEnd_717658 := by exact prefixLift 717658
  have htrace : WordTrace (prefixWord ++ tailWord_717658) baseStart_717658 baseEnd_717658 := by
    simpa [prefixWord, tailWord_717658, baseEnd_717658] using wordTrace_append hprefix tailTrace_717658
  have hstable : (prefixWord ++ tailWord_717658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717658).length < 2 ^ (prefixWord ++ tailWord_717658).sum := by decide
  have hdescent : baseEnd_717658 < baseStart_717658 := by decide
  rcases family_descends (prefixWord ++ tailWord_717658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717668 : List Nat := [2, 3, 1, 1, 4, 3, 2, 7]
def baseStart_717668 : Nat := 118140960795 + 717668 * 2 ^ 59
def prefixEnd_717668 : Nat := 4983230072969 + 3 ^ 40 * 717668 * 2
def baseEnd_717668 : Nat := 13648467938926050161093

theorem tailTrace_717668 : CollatzResearch.WordTrace tailWord_717668 prefixEnd_717668 13648467938926050161093 := by
  unfold tailWord_717668
  simp only [CollatzResearch.WordTrace]
  refine ⟨13087751182009439390688829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17450334909345919187585105 13087751182009439390688829)
  ·
    refine ⟨4907906693253539771508311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13087751182009439390688829 4907906693253539771508311)
    ·
      refine ⟨7361860039880309657262467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4907906693253539771508311 7361860039880309657262467)
      ·
        refine ⟨11042790059820464485893701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7361860039880309657262467 11042790059820464485893701)
        ·
          refine ⟨2070523136216337091105069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11042790059820464485893701 2070523136216337091105069)
          ·
            refine ⟨776446176081126409164401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2070523136216337091105069 776446176081126409164401)
            ·
              refine ⟨582334632060844806873301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 776446176081126409164401 582334632060844806873301)
              ·
                refine ⟨13648467938926050161093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 582334632060844806873301 13648467938926050161093)
                ·
                  rfl

theorem cell23_717668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 7].length) (baseStart_717668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717668 prefixEnd_717668 := by exact prefixLift 717668
  have htrace : WordTrace (prefixWord ++ tailWord_717668) baseStart_717668 baseEnd_717668 := by
    simpa [prefixWord, tailWord_717668, baseEnd_717668] using wordTrace_append hprefix tailTrace_717668
  have hstable : (prefixWord ++ tailWord_717668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717668).length < 2 ^ (prefixWord ++ tailWord_717668).sum := by decide
  have hdescent : baseEnd_717668 < baseStart_717668 := by decide
  rcases family_descends (prefixWord ++ tailWord_717668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717752 : List Nat := [2, 1, 2, 1, 2, 5, 2, 2, 2, 2, 2]
def baseStart_717752 : Nat := 118140960795 + 717752 * 2 ^ 59
def prefixEnd_717752 : Nat := 4983230072969 + 3 ^ 40 * 717752 * 2
def baseEnd_717752 : Nat := 368551766725981025699125

theorem tailTrace_717752 : CollatzResearch.WordTrace tailWord_717752 prefixEnd_717752 368551766725981025699125 := by
  unfold tailWord_717752
  simp only [CollatzResearch.WordTrace]
  refine ⟨13089283047857280563717755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17452377397143040751623673 13089283047857280563717755)
  ·
    refine ⟨19633924571785920845576633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13089283047857280563717755 19633924571785920845576633)
    ·
      refine ⟨14725443428839440634182475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19633924571785920845576633 14725443428839440634182475)
      ·
        refine ⟨22088165143259160951273713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14725443428839440634182475 22088165143259160951273713)
        ·
          refine ⟨16566123857444370713455285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22088165143259160951273713 16566123857444370713455285)
          ·
            refine ⟨1553074111635409754386433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16566123857444370713455285 1553074111635409754386433)
            ·
              refine ⟨1164805583726557315789825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1553074111635409754386433 1164805583726557315789825)
              ·
                refine ⟨873604187794917986842369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1164805583726557315789825 873604187794917986842369)
                ·
                  refine ⟨655203140846188490131777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 873604187794917986842369 655203140846188490131777)
                  ·
                    refine ⟨491402355634641367598833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 655203140846188490131777 491402355634641367598833)
                    ·
                      refine ⟨368551766725981025699125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 491402355634641367598833 368551766725981025699125)
                      ·
                        rfl

theorem cell23_717752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 2, 2, 2].length) (baseStart_717752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717752 prefixEnd_717752 := by exact prefixLift 717752
  have htrace : WordTrace (prefixWord ++ tailWord_717752) baseStart_717752 baseEnd_717752 := by
    simpa [prefixWord, tailWord_717752, baseEnd_717752] using wordTrace_append hprefix tailTrace_717752
  have hstable : (prefixWord ++ tailWord_717752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717752).length < 2 ^ (prefixWord ++ tailWord_717752).sum := by decide
  have hdescent : baseEnd_717752 < baseStart_717752 := by decide
  rcases family_descends (prefixWord ++ tailWord_717752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717821 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_717821 : Nat := 118140960795 + 717821 * 2 ^ 59
def prefixEnd_717821 : Nat := 4983230072969 + 3 ^ 40 * 717821 * 2
def baseEnd_717821 : Nat := 368587196891141255736307

theorem tailTrace_717821 : CollatzResearch.WordTrace tailWord_717821 prefixEnd_717821 368587196891141255736307 := by
  unfold tailWord_717821
  simp only [CollatzResearch.WordTrace]
  refine ⟨26181082732464585911697317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17454055154976390607798211 26181082732464585911697317)
  ·
    refine ⟨4908953012337109858443247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26181082732464585911697317 4908953012337109858443247)
    ·
      refine ⟨7363429518505664787664871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4908953012337109858443247 7363429518505664787664871)
      ·
        refine ⟨11045144277758497181497307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7363429518505664787664871 11045144277758497181497307)
        ·
          refine ⟨16567716416637745772245961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11045144277758497181497307 16567716416637745772245961)
          ·
            refine ⟨12425787312478309329184471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16567716416637745772245961 12425787312478309329184471)
            ·
              refine ⟨18638680968717463993776707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12425787312478309329184471 18638680968717463993776707)
              ·
                refine ⟨27958021453076195990665061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18638680968717463993776707 27958021453076195990665061)
                ·
                  refine ⟨5242129022451786748249699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27958021453076195990665061 5242129022451786748249699)
                  ·
                    refine ⟨7863193533677680122374549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5242129022451786748249699 7863193533677680122374549)
                    ·
                      refine ⟨368587196891141255736307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7863193533677680122374549 368587196891141255736307)
                      ·
                        rfl

theorem cell23_717821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_717821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717821 prefixEnd_717821 := by exact prefixLift 717821
  have htrace : WordTrace (prefixWord ++ tailWord_717821) baseStart_717821 baseEnd_717821 := by
    simpa [prefixWord, tailWord_717821, baseEnd_717821] using wordTrace_append hprefix tailTrace_717821
  have hstable : (prefixWord ++ tailWord_717821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717821).length < 2 ^ (prefixWord ++ tailWord_717821).sum := by decide
  have hdescent : baseEnd_717821 < baseStart_717821 := by decide
  rcases family_descends (prefixWord ++ tailWord_717821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717825 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 2, 4, 2]
def baseStart_717825 : Nat := 118140960795 + 717825 * 2 ^ 59
def prefixEnd_717825 : Nat := 4983230072969 + 3 ^ 40 * 717825 * 2
def baseEnd_717825 : Nat := 368589250813759240086289

theorem tailTrace_717825 : CollatzResearch.WordTrace tailWord_717825 prefixEnd_717825 368589250813759240086289 := by
  unfold tailWord_717825
  simp only [CollatzResearch.WordTrace]
  refine ⟨26181228624450094594842929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17454152416300063063228619 26181228624450094594842929)
  ·
    refine ⟨19635921468337570946132197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26181228624450094594842929 19635921468337570946132197)
    ·
      refine ⟨3681735275313294552399787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19635921468337570946132197 3681735275313294552399787)
      ·
        refine ⟨5522602912969941828599681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3681735275313294552399787 5522602912969941828599681)
        ·
          refine ⟨4141952184727456371449761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5522602912969941828599681 4141952184727456371449761)
          ·
            refine ⟨3106464138545592278587321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4141952184727456371449761 3106464138545592278587321)
            ·
              refine ⟨2329848103909194208940491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3106464138545592278587321 2329848103909194208940491)
              ·
                refine ⟨3494772155863791313410737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2329848103909194208940491 3494772155863791313410737)
                ·
                  refine ⟨2621079116897843485058053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3494772155863791313410737 2621079116897843485058053)
                  ·
                    refine ⟨491452334418345653448385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2621079116897843485058053 491452334418345653448385)
                    ·
                      refine ⟨368589250813759240086289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 491452334418345653448385 368589250813759240086289)
                      ·
                        rfl

theorem cell23_717825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_717825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717825 prefixEnd_717825 := by exact prefixLift 717825
  have htrace : WordTrace (prefixWord ++ tailWord_717825) baseStart_717825 baseEnd_717825 := by
    simpa [prefixWord, tailWord_717825, baseEnd_717825] using wordTrace_append hprefix tailTrace_717825
  have hstable : (prefixWord ++ tailWord_717825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717825).length < 2 ^ (prefixWord ++ tailWord_717825).sum := by decide
  have hdescent : baseEnd_717825 < baseStart_717825 := by decide
  rcases family_descends (prefixWord ++ tailWord_717825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717895 : List Nat := [1, 1, 4, 1, 3, 2, 3, 2, 1, 5]
def baseStart_717895 : Nat := 118140960795 + 717895 * 2 ^ 59
def prefixEnd_717895 : Nat := 4983230072969 + 3 ^ 40 * 717895 * 2
def baseEnd_717895 : Nat := 122875064819857988736989

theorem tailTrace_717895 : CollatzResearch.WordTrace tailWord_717895 prefixEnd_717895 122875064819857988736989 := by
  unfold tailWord_717895
  simp only [CollatzResearch.WordTrace]
  refine ⟨26183781734196496549891139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17455854489464331033260759 26183781734196496549891139)
  ·
    refine ⟨39275672601294744824836709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26183781734196496549891139 39275672601294744824836709)
    ·
      refine ⟨7364188612742764654656883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39275672601294744824836709 7364188612742764654656883)
      ·
        refine ⟨11046282919114146981985325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7364188612742764654656883 11046282919114146981985325)
        ·
          refine ⟨4142356094667805118244497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11046282919114146981985325 4142356094667805118244497)
          ·
            refine ⟨3106767071000853838683373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4142356094667805118244497 3106767071000853838683373)
            ·
              refine ⟨1165037651625320189506265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3106767071000853838683373 1165037651625320189506265)
              ·
                refine ⟨873778238718990142129699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1165037651625320189506265 873778238718990142129699)
                ·
                  refine ⟨1310667358078485213194549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 873778238718990142129699 1310667358078485213194549)
                  ·
                    refine ⟨122875064819857988736989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1310667358078485213194549 122875064819857988736989)
                    ·
                      rfl

theorem cell23_717895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_717895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717895 prefixEnd_717895 := by exact prefixLift 717895
  have htrace : WordTrace (prefixWord ++ tailWord_717895) baseStart_717895 baseEnd_717895 := by
    simpa [prefixWord, tailWord_717895, baseEnd_717895] using wordTrace_append hprefix tailTrace_717895
  have hstable : (prefixWord ++ tailWord_717895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717895).length < 2 ^ (prefixWord ++ tailWord_717895).sum := by decide
  have hdescent : baseEnd_717895 < baseStart_717895 := by decide
  rcases family_descends (prefixWord ++ tailWord_717895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717902 : List Nat := [4, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2]
def baseStart_717902 : Nat := 118140960795 + 717902 * 2 ^ 59
def prefixEnd_717902 : Nat := 4983230072969 + 3 ^ 40 * 717902 * 2
def baseEnd_717902 : Nat := 368628788824155438823435

theorem tailTrace_717902 : CollatzResearch.WordTrace tailWord_717902 prefixEnd_717902 368628788824155438823435 := by
  unfold tailWord_717902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3273004630646392093174495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17456024696780757830263973 3273004630646392093174495)
  ·
    refine ⟨4909506945969588139761743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3273004630646392093174495 4909506945969588139761743)
    ·
      refine ⟨7364260418954382209642615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4909506945969588139761743 7364260418954382209642615)
      ·
        refine ⟨11046390628431573314463923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7364260418954382209642615 11046390628431573314463923)
        ·
          refine ⟨16569585942647359971695885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11046390628431573314463923 16569585942647359971695885)
          ·
            refine ⟨6213594728492759989385957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16569585942647359971695885 6213594728492759989385957)
            ·
              refine ⟨1165049011592392498009867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6213594728492759989385957 1165049011592392498009867)
              ·
                refine ⟨1747573517388588747014801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165049011592392498009867 1747573517388588747014801)
                ·
                  refine ⟨1310680138041441560261101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1747573517388588747014801 1310680138041441560261101)
                  ·
                    refine ⟨491505051765540585097913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1310680138041441560261101 491505051765540585097913)
                    ·
                      refine ⟨368628788824155438823435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 491505051765540585097913 368628788824155438823435)
                      ·
                        rfl

theorem cell23_717902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_717902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717902 prefixEnd_717902 := by exact prefixLift 717902
  have htrace : WordTrace (prefixWord ++ tailWord_717902) baseStart_717902 baseEnd_717902 := by
    simpa [prefixWord, tailWord_717902, baseEnd_717902] using wordTrace_append hprefix tailTrace_717902
  have hstable : (prefixWord ++ tailWord_717902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717902).length < 2 ^ (prefixWord ++ tailWord_717902).sum := by decide
  have hdescent : baseEnd_717902 < baseStart_717902 := by decide
  rcases family_descends (prefixWord ++ tailWord_717902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717908 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_717908 : Nat := 118140960795 + 717908 * 2 ^ 59
def prefixEnd_717908 : Nat := 4983230072969 + 3 ^ 40 * 717908 * 2
def baseEnd_717908 : Nat := 122877289902694138449469

theorem tailTrace_717908 : CollatzResearch.WordTrace tailWord_717908 prefixEnd_717908 122877289902694138449469 := by
  unfold tailWord_717908
  simp only [CollatzResearch.WordTrace]
  refine ⟨13092127941574699885057189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17456170588766266513409585 13092127941574699885057189)
  ·
    refine ⟨2454773989045256228448223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13092127941574699885057189 2454773989045256228448223)
    ·
      refine ⟨3682160983567884342672335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2454773989045256228448223 3682160983567884342672335)
      ·
        refine ⟨5523241475351826514008503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3682160983567884342672335 5523241475351826514008503)
        ·
          refine ⟨8284862213027739771012755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5523241475351826514008503 8284862213027739771012755)
          ·
            refine ⟨12427293319541609656519133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8284862213027739771012755 12427293319541609656519133)
            ·
              refine ⟨4660234994828103621194675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12427293319541609656519133 4660234994828103621194675)
              ·
                refine ⟨6990352492242155431792013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4660234994828103621194675 6990352492242155431792013)
                ·
                  refine ⟨2621382184590808286922005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6990352492242155431792013 2621382184590808286922005)
                  ·
                    refine ⟨122877289902694138449469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2621382184590808286922005 122877289902694138449469)
                    ·
                      rfl

theorem cell23_717908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_717908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717908 prefixEnd_717908 := by exact prefixLift 717908
  have htrace : WordTrace (prefixWord ++ tailWord_717908) baseStart_717908 baseEnd_717908 := by
    simpa [prefixWord, tailWord_717908, baseEnd_717908] using wordTrace_append hprefix tailTrace_717908
  have hstable : (prefixWord ++ tailWord_717908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717908).length < 2 ^ (prefixWord ++ tailWord_717908).sum := by decide
  have hdescent : baseEnd_717908 < baseStart_717908 := by decide
  rcases family_descends (prefixWord ++ tailWord_717908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717932 : List Nat := [2, 2, 1, 1, 3, 2, 2, 3, 3, 2, 2]
def baseStart_717932 : Nat := 118140960795 + 717932 * 2 ^ 59
def prefixEnd_717932 : Nat := 4983230072969 + 3 ^ 40 * 717932 * 2
def baseEnd_717932 : Nat := 368644193243790321448297

theorem tailTrace_717932 : CollatzResearch.WordTrace tailWord_717932 prefixEnd_717932 368644193243790321448297 := by
  unfold tailWord_717932
  simp only [CollatzResearch.WordTrace]
  refine ⟨13092565617531225934494025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17456754156708301245992033 13092565617531225934494025)
  ·
    refine ⟨9819424213148419450870519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13092565617531225934494025 9819424213148419450870519)
    ·
      refine ⟨14729136319722629176305779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9819424213148419450870519 14729136319722629176305779)
      ·
        refine ⟨22093704479583943764458669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14729136319722629176305779 22093704479583943764458669)
        ·
          refine ⟨8285139179843978911672001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22093704479583943764458669 8285139179843978911672001)
          ·
            refine ⟨6213854384882984183754001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8285139179843978911672001 6213854384882984183754001)
            ·
              refine ⟨4660390788662238137815501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6213854384882984183754001 4660390788662238137815501)
              ·
                refine ⟨1747646545748339301680813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4660390788662238137815501 1747646545748339301680813)
                ·
                  refine ⟨655367454655627238130305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1747646545748339301680813 655367454655627238130305)
                  ·
                    refine ⟨491525590991720428597729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 655367454655627238130305 491525590991720428597729)
                    ·
                      refine ⟨368644193243790321448297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 491525590991720428597729 368644193243790321448297)
                      ·
                        rfl

theorem cell23_717932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 2, 2].length) (baseStart_717932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717932 prefixEnd_717932 := by exact prefixLift 717932
  have htrace : WordTrace (prefixWord ++ tailWord_717932) baseStart_717932 baseEnd_717932 := by
    simpa [prefixWord, tailWord_717932, baseEnd_717932] using wordTrace_append hprefix tailTrace_717932
  have hstable : (prefixWord ++ tailWord_717932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717932).length < 2 ^ (prefixWord ++ tailWord_717932).sum := by decide
  have hdescent : baseEnd_717932 < baseStart_717932 := by decide
  rcases family_descends (prefixWord ++ tailWord_717932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717942 : List Nat := [5, 1, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_717942 : Nat := 118140960795 + 717942 * 2 ^ 59
def prefixEnd_717942 : Nat := 4983230072969 + 3 ^ 40 * 717942 * 2
def baseEnd_717942 : Nat := 122883109350111760774417

theorem tailTrace_717942 : CollatzResearch.WordTrace tailWord_717942 prefixEnd_717942 122883109350111760774417 := by
  unfold tailWord_717942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1636593497814138973553255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17456997310017482384568053 1636593497814138973553255)
  ·
    refine ⟨2454890246721208460329883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1636593497814138973553255 2454890246721208460329883)
    ·
      refine ⟨3682335370081812690494825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2454890246721208460329883 3682335370081812690494825)
      ·
        refine ⟨2761751527561359517871119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3682335370081812690494825 2761751527561359517871119)
        ·
          refine ⟨4142627291342039276806679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2761751527561359517871119 4142627291342039276806679)
          ·
            refine ⟨6213940937013058915210019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4142627291342039276806679 6213940937013058915210019)
            ·
              refine ⟨9320911405519588372815029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6213940937013058915210019 9320911405519588372815029)
              ·
                refine ⟨873835444267461409951409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9320911405519588372815029 873835444267461409951409)
                ·
                  refine ⟨655376583200596057463557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 873835444267461409951409 655376583200596057463557)
                  ·
                    refine ⟨122883109350111760774417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 655376583200596057463557 122883109350111760774417)
                    ·
                      rfl

theorem cell23_717942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_717942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717942 prefixEnd_717942 := by exact prefixLift 717942
  have htrace : WordTrace (prefixWord ++ tailWord_717942) baseStart_717942 baseEnd_717942 := by
    simpa [prefixWord, tailWord_717942, baseEnd_717942] using wordTrace_append hprefix tailTrace_717942
  have hstable : (prefixWord ++ tailWord_717942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717942).length < 2 ^ (prefixWord ++ tailWord_717942).sum := by decide
  have hdescent : baseEnd_717942 < baseStart_717942 := by decide
  rcases family_descends (prefixWord ++ tailWord_717942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717966 : List Nat := [4, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2]
def baseStart_717966 : Nat := 118140960795 + 717966 * 2 ^ 59
def prefixEnd_717966 : Nat := 4983230072969 + 3 ^ 40 * 717966 * 2
def baseEnd_717966 : Nat := 368661651586043188423141

theorem tailTrace_717966 : CollatzResearch.WordTrace tailWord_717966 prefixEnd_717966 368661651586043188423141 := by
  unfold tailWord_717966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3273296414617409459465719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17457580877959517117150501 3273296414617409459465719)
  ·
    refine ⟨4909944621926114189198579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3273296414617409459465719 4909944621926114189198579)
    ·
      refine ⟨7364916932889171283797869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4909944621926114189198579 7364916932889171283797869)
      ·
        refine ⟨2761843849833439231424201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7364916932889171283797869 2761843849833439231424201)
        ·
          refine ⟨2071382887375079423568151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2761843849833439231424201 2071382887375079423568151)
          ·
            refine ⟨3107074331062619135352227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2071382887375079423568151 3107074331062619135352227)
            ·
              refine ⟨4660611496593928703028341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3107074331062619135352227 4660611496593928703028341)
              ·
                refine ⟨436932327805680815908907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4660611496593928703028341 436932327805680815908907)
                ·
                  refine ⟨655398491708521223863361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 436932327805680815908907 655398491708521223863361)
                  ·
                    refine ⟨491548868781390917897521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 655398491708521223863361 491548868781390917897521)
                    ·
                      refine ⟨368661651586043188423141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 491548868781390917897521 368661651586043188423141)
                      ·
                        rfl

theorem cell23_717966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_717966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_717966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_717966 prefixEnd_717966 := by exact prefixLift 717966
  have htrace : WordTrace (prefixWord ++ tailWord_717966) baseStart_717966 baseEnd_717966 := by
    simpa [prefixWord, tailWord_717966, baseEnd_717966] using wordTrace_append hprefix tailTrace_717966
  have hstable : (prefixWord ++ tailWord_717966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717966).length < 2 ^ (prefixWord ++ tailWord_717966).sum := by decide
  have hdescent : baseEnd_717966 < baseStart_717966 := by decide
  rcases family_descends (prefixWord ++ tailWord_717966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718006 : List Nat := [5, 1, 3, 2, 1, 2, 2, 7]
def baseStart_718006 : Nat := 118140960795 + 718006 * 2 ^ 59
def prefixEnd_718006 : Nat := 4983230072969 + 3 ^ 40 * 718006 * 2
def baseEnd_718006 : Nat := 13654895956008260441591

theorem tailTrace_718006 : CollatzResearch.WordTrace tailWord_718006 prefixEnd_718006 13654895956008260441591 := by
  unfold tailWord_718006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1636739389799647656698867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17458553491196241671454581 1636739389799647656698867)
  ·
    refine ⟨2455109084699471485048301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1636739389799647656698867 2455109084699471485048301)
    ·
      refine ⟨920665906762301806893113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2455109084699471485048301 920665906762301806893113)
      ·
        refine ⟨690499430071726355169835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 920665906762301806893113 690499430071726355169835)
        ·
          refine ⟨1035749145107589532754753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 690499430071726355169835 1035749145107589532754753)
          ·
            refine ⟨776811858830692149566065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1035749145107589532754753 776811858830692149566065)
            ·
              refine ⟨582608894123019112174549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 776811858830692149566065 582608894123019112174549)
              ·
                refine ⟨13654895956008260441591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 582608894123019112174549 13654895956008260441591)
                ·
                  rfl

theorem cell23_718006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_718006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718006 prefixEnd_718006 := by exact prefixLift 718006
  have htrace : WordTrace (prefixWord ++ tailWord_718006) baseStart_718006 baseEnd_718006 := by
    simpa [prefixWord, tailWord_718006, baseEnd_718006] using wordTrace_append hprefix tailTrace_718006
  have hstable : (prefixWord ++ tailWord_718006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718006).length < 2 ^ (prefixWord ++ tailWord_718006).sum := by decide
  have hdescent : baseEnd_718006 < baseStart_718006 := by decide
  rcases family_descends (prefixWord ++ tailWord_718006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718009 : List Nat := [1, 2, 1, 4, 1, 4, 2, 2, 1, 3, 2]
def baseStart_718009 : Nat := 118140960795 + 718009 * 2 ^ 59
def prefixEnd_718009 : Nat := 4983230072969 + 3 ^ 40 * 718009 * 2
def baseEnd_718009 : Nat := 368683731254186520185443

theorem tailTrace_718009 : CollatzResearch.WordTrace tailWord_718009 prefixEnd_718009 368683731254186520185443 := by
  unfold tailWord_718009
  simp only [CollatzResearch.WordTrace]
  refine ⟨26187939655783494019541081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17458626437188996013027387 26187939655783494019541081)
  ·
    refine ⟨19640954741837620514655811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26187939655783494019541081 19640954741837620514655811)
    ·
      refine ⟨29461432112756430771983717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19640954741837620514655811 29461432112756430771983717)
      ·
        refine ⟨5524018521141830769746947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29461432112756430771983717 5524018521141830769746947)
        ·
          refine ⟨8286027781712746154620421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5524018521141830769746947 8286027781712746154620421)
          ·
            refine ⟨1553630209071139903991329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8286027781712746154620421 1553630209071139903991329)
            ·
              refine ⟨1165222656803354927993497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1553630209071139903991329 1165222656803354927993497)
              ·
                refine ⟨873916992602516195995123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1165222656803354927993497 873916992602516195995123)
                ·
                  refine ⟨1310875488903774293992685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 873916992602516195995123 1310875488903774293992685)
                  ·
                    refine ⟨491578308338915360247257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1310875488903774293992685 491578308338915360247257)
                    ·
                      refine ⟨368683731254186520185443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 491578308338915360247257 368683731254186520185443)
                      ·
                        rfl

theorem cell23_718009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_718009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718009 prefixEnd_718009 := by exact prefixLift 718009
  have htrace : WordTrace (prefixWord ++ tailWord_718009) baseStart_718009 baseEnd_718009 := by
    simpa [prefixWord, tailWord_718009, baseEnd_718009] using wordTrace_append hprefix tailTrace_718009
  have hstable : (prefixWord ++ tailWord_718009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718009).length < 2 ^ (prefixWord ++ tailWord_718009).sum := by decide
  have hdescent : baseEnd_718009 < baseStart_718009 := by decide
  rcases family_descends (prefixWord ++ tailWord_718009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718105 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 9, 4]
def baseStart_718105 : Nat := 118140960795 + 718105 * 2 ^ 59
def prefixEnd_718105 : Nat := 4983230072969 + 3 ^ 40 * 718105 * 2
def baseEnd_718105 : Nat := 122911008465672714861667

theorem tailTrace_718105 : CollatzResearch.WordTrace tailWord_718105 prefixEnd_718105 122911008465672714861667 := by
  unfold tailWord_718105
  simp only [CollatzResearch.WordTrace]
  refine ⟨26191441063435702415035769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17460960708957134943357179 26191441063435702415035769)
  ·
    refine ⟨19643580797576776811276827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26191441063435702415035769 19643580797576776811276827)
    ·
      refine ⟨29465371196365165216915241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19643580797576776811276827 29465371196365165216915241)
      ·
        refine ⟨22099028397273873912686431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29465371196365165216915241 22099028397273873912686431)
        ·
          refine ⟨33148542595910810869029647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22099028397273873912686431 33148542595910810869029647)
          ·
            refine ⟨49722813893866216303544471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33148542595910810869029647 49722813893866216303544471)
            ·
              refine ⟨74584220840799324455316707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49722813893866216303544471 74584220840799324455316707)
              ·
                refine ⟨111876331261198986682975061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74584220840799324455316707 111876331261198986682975061)
                ·
                  refine ⟨655525378483587812595557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 111876331261198986682975061 655525378483587812595557)
                  ·
                    refine ⟨122911008465672714861667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 655525378483587812595557 122911008465672714861667)
                    ·
                      rfl

theorem cell23_718105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 4].length) (baseStart_718105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718105 prefixEnd_718105 := by exact prefixLift 718105
  have htrace : WordTrace (prefixWord ++ tailWord_718105) baseStart_718105 baseEnd_718105 := by
    simpa [prefixWord, tailWord_718105, baseEnd_718105] using wordTrace_append hprefix tailTrace_718105
  have hstable : (prefixWord ++ tailWord_718105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718105).length < 2 ^ (prefixWord ++ tailWord_718105).sum := by decide
  have hdescent : baseEnd_718105 < baseStart_718105 := by decide
  rcases family_descends (prefixWord ++ tailWord_718105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718129 : List Nat := [1, 2, 2, 3, 3, 3, 1, 1, 2, 1, 4]
def baseStart_718129 : Nat := 118140960795 + 718129 * 2 ^ 59
def prefixEnd_718129 : Nat := 4983230072969 + 3 ^ 40 * 718129 * 2
def baseEnd_718129 : Nat := 368745348932726050684891

theorem tailTrace_718129 : CollatzResearch.WordTrace tailWord_718129 prefixEnd_718129 368745348932726050684891 := by
  unfold tailWord_718129
  simp only [CollatzResearch.WordTrace]
  refine ⟨26192316415348754513909441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17461544276899169675939627 26192316415348754513909441)
  ·
    refine ⟨19644237311511565885432081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26192316415348754513909441 19644237311511565885432081)
    ·
      refine ⟨14733177983633674414074061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19644237311511565885432081 14733177983633674414074061)
      ·
        refine ⟨5524941743862627905277773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14733177983633674414074061 5524941743862627905277773)
        ·
          refine ⟨2071853153948485464479165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5524941743862627905277773 2071853153948485464479165)
          ·
            refine ⟨776944932730682049179687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2071853153948485464479165 776944932730682049179687)
            ·
              refine ⟨1165417399096023073769531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 776944932730682049179687 1165417399096023073769531)
              ·
                refine ⟨1748126098644034610654297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165417399096023073769531 1748126098644034610654297)
                ·
                  refine ⟨1311094573983025957990723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1748126098644034610654297 1311094573983025957990723)
                  ·
                    refine ⟨1966641860974538936986085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1311094573983025957990723 1966641860974538936986085)
                    ·
                      refine ⟨368745348932726050684891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1966641860974538936986085 368745348932726050684891)
                      ·
                        rfl

theorem cell23_718129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_718129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718129 prefixEnd_718129 := by exact prefixLift 718129
  have htrace : WordTrace (prefixWord ++ tailWord_718129) baseStart_718129 baseEnd_718129 := by
    simpa [prefixWord, tailWord_718129, baseEnd_718129] using wordTrace_append hprefix tailTrace_718129
  have hstable : (prefixWord ++ tailWord_718129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718129).length < 2 ^ (prefixWord ++ tailWord_718129).sum := by decide
  have hdescent : baseEnd_718129 < baseStart_718129 := by decide
  rcases family_descends (prefixWord ++ tailWord_718129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718179 : List Nat := [1, 1, 1, 5, 2, 2, 2, 2, 3, 1, 3]
def baseStart_718179 : Nat := 118140960795 + 718179 * 2 ^ 59
def prefixEnd_718179 : Nat := 4983230072969 + 3 ^ 40 * 718179 * 2
def baseEnd_718179 : Nat := 368771022965450855059661

theorem tailTrace_718179 : CollatzResearch.WordTrace tailWord_718179 prefixEnd_718179 368771022965450855059661 := by
  unfold tailWord_718179
  simp only [CollatzResearch.WordTrace]
  refine ⟨26194140065167613053229591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17462760043445075368819727 26194140065167613053229591)
  ·
    refine ⟨39291210097751419579844387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26194140065167613053229591 39291210097751419579844387)
    ·
      refine ⟨58936815146627129369766581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39291210097751419579844387 58936815146627129369766581)
      ·
        refine ⟨5525326419996293378415617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58936815146627129369766581 5525326419996293378415617)
        ·
          refine ⟨4143994814997220033811713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5525326419996293378415617 4143994814997220033811713)
          ·
            refine ⟨3107996111247915025358785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4143994814997220033811713 3107996111247915025358785)
            ·
              refine ⟨2330997083435936269019089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3107996111247915025358785 2330997083435936269019089)
              ·
                refine ⟨1748247812576952201764317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2330997083435936269019089 1748247812576952201764317)
                ·
                  refine ⟨655592929716357075661619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1748247812576952201764317 655592929716357075661619)
                  ·
                    refine ⟨983389394574535613492429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 655592929716357075661619 983389394574535613492429)
                    ·
                      refine ⟨368771022965450855059661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 983389394574535613492429 368771022965450855059661)
                      ·
                        rfl

theorem cell23_718179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_718179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718179 prefixEnd_718179 := by exact prefixLift 718179
  have htrace : WordTrace (prefixWord ++ tailWord_718179) baseStart_718179 baseEnd_718179 := by
    simpa [prefixWord, tailWord_718179, baseEnd_718179] using wordTrace_append hprefix tailTrace_718179
  have hstable : (prefixWord ++ tailWord_718179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718179).length < 2 ^ (prefixWord ++ tailWord_718179).sum := by decide
  have hdescent : baseEnd_718179 < baseStart_718179 := by decide
  rcases family_descends (prefixWord ++ tailWord_718179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718189 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 1, 5, 2]
def baseStart_718189 : Nat := 118140960795 + 718189 * 2 ^ 59
def prefixEnd_718189 : Nat := 4983230072969 + 3 ^ 40 * 718189 * 2
def baseEnd_718189 : Nat := 368776157771995815934615

theorem tailTrace_718189 : CollatzResearch.WordTrace tailWord_718189 prefixEnd_718189 368776157771995815934615 := by
  unfold tailWord_718189
  simp only [CollatzResearch.WordTrace]
  refine ⟨26194504795131384761093621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17463003196754256507395747 26194504795131384761093621)
  ·
    refine ⟨2455734824543567321352527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26194504795131384761093621 2455734824543567321352527)
    ·
      refine ⟨3683602236815350982028791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2455734824543567321352527 3683602236815350982028791)
      ·
        refine ⟨5525403355223026473043187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3683602236815350982028791 5525403355223026473043187)
        ·
          refine ⟨8288105032834539709564781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5525403355223026473043187 8288105032834539709564781)
          ·
            refine ⟨3108039387312952391086793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8288105032834539709564781 3108039387312952391086793)
            ·
              refine ⟨2331029540484714293315095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3108039387312952391086793 2331029540484714293315095)
              ·
                refine ⟨3496544310727071439972643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331029540484714293315095 3496544310727071439972643)
                ·
                  refine ⟨5244816466090607159958965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3496544310727071439972643 5244816466090607159958965)
                  ·
                    refine ⟨491701543695994421246153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5244816466090607159958965 491701543695994421246153)
                    ·
                      refine ⟨368776157771995815934615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 491701543695994421246153 368776157771995815934615)
                      ·
                        rfl

theorem cell23_718189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_718189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718189 prefixEnd_718189 := by exact prefixLift 718189
  have htrace : WordTrace (prefixWord ++ tailWord_718189) baseStart_718189 baseEnd_718189 := by
    simpa [prefixWord, tailWord_718189, baseEnd_718189] using wordTrace_append hprefix tailTrace_718189
  have hstable : (prefixWord ++ tailWord_718189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718189).length < 2 ^ (prefixWord ++ tailWord_718189).sum := by decide
  have hdescent : baseEnd_718189 < baseStart_718189 := by decide
  rcases family_descends (prefixWord ++ tailWord_718189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718190 : List Nat := [4, 1, 2, 4, 1, 2, 1, 3, 1, 4]
def baseStart_718190 : Nat := 118140960795 + 718190 * 2 ^ 59
def prefixEnd_718190 : Nat := 4983230072969 + 3 ^ 40 * 718190 * 2
def baseEnd_718190 : Nat := 122925557084216770674037

theorem tailTrace_718190 : CollatzResearch.WordTrace tailWord_718190 prefixEnd_718190 122925557084216770674037 := by
  unfold tailWord_718190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3274317658515970241485003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17463027512085174621253349 3274317658515970241485003)
  ·
    refine ⟨4911476487773955362227505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3274317658515970241485003 4911476487773955362227505)
    ·
      refine ⟨3683607365830466521670629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4911476487773955362227505 3683607365830466521670629)
      ·
        refine ⟨690676381093212472813243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3683607365830466521670629 690676381093212472813243)
        ·
          refine ⟨1036014571639818709219865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 690676381093212472813243 1036014571639818709219865)
          ·
            refine ⟨777010928729864031914899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1036014571639818709219865 777010928729864031914899)
            ·
              refine ⟨1165516393094796047872349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777010928729864031914899 1165516393094796047872349)
              ·
                refine ⟨437068647410548517952131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1165516393094796047872349 437068647410548517952131)
                ·
                  refine ⟨655602971115822776928197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 437068647410548517952131 655602971115822776928197)
                  ·
                    refine ⟨122925557084216770674037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 655602971115822776928197 122925557084216770674037)
                    ·
                      rfl

theorem cell23_718190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_718190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718190 prefixEnd_718190 := by exact prefixLift 718190
  have htrace : WordTrace (prefixWord ++ tailWord_718190) baseStart_718190 baseEnd_718190 := by
    simpa [prefixWord, tailWord_718190, baseEnd_718190] using wordTrace_append hprefix tailTrace_718190
  have hstable : (prefixWord ++ tailWord_718190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718190).length < 2 ^ (prefixWord ++ tailWord_718190).sum := by decide
  have hdescent : baseEnd_718190 < baseStart_718190 := by decide
  rcases family_descends (prefixWord ++ tailWord_718190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718202 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2]
def baseStart_718202 : Nat := 118140960795 + 718202 * 2 ^ 59
def prefixEnd_718202 : Nat := 4983230072969 + 3 ^ 40 * 718202 * 2
def baseEnd_718202 : Nat := 368782833020504265072055

theorem tailTrace_718202 : CollatzResearch.WordTrace tailWord_718202 prefixEnd_718202 368782833020504265072055 := by
  unfold tailWord_718202
  simp only [CollatzResearch.WordTrace]
  refine ⟨6548744736021071995329215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17463319296056191987544573 6548744736021071995329215)
  ·
    refine ⟨9823117104031607992993823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6548744736021071995329215 9823117104031607992993823)
    ·
      refine ⟨14734675656047411989490735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9823117104031607992993823 14734675656047411989490735)
      ·
        refine ⟨22102013484071117984236103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14734675656047411989490735 22102013484071117984236103)
        ·
          refine ⟨33153020226106676976354155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22102013484071117984236103 33153020226106676976354155)
          ·
            refine ⟨49729530339160015464531233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33153020226106676976354155 49729530339160015464531233)
            ·
              refine ⟨37297147754370011598398425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49729530339160015464531233 37297147754370011598398425)
              ·
                refine ⟨27972860815777508698798819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37297147754370011598398425 27972860815777508698798819)
                ·
                  refine ⟨41959291223666263048198229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27972860815777508698798819 41959291223666263048198229)
                  ·
                    refine ⟨491710444027339020096073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41959291223666263048198229 491710444027339020096073)
                    ·
                      refine ⟨368782833020504265072055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 491710444027339020096073 368782833020504265072055)
                      ·
                        rfl

theorem cell23_718202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2].length) (baseStart_718202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718202 prefixEnd_718202 := by exact prefixLift 718202
  have htrace : WordTrace (prefixWord ++ tailWord_718202) baseStart_718202 baseEnd_718202 := by
    simpa [prefixWord, tailWord_718202, baseEnd_718202] using wordTrace_append hprefix tailTrace_718202
  have hstable : (prefixWord ++ tailWord_718202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718202).length < 2 ^ (prefixWord ++ tailWord_718202).sum := by decide
  have hdescent : baseEnd_718202 < baseStart_718202 := by decide
  rcases family_descends (prefixWord ++ tailWord_718202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718236 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_718236 : Nat := 118140960795 + 718236 * 2 ^ 59
def prefixEnd_718236 : Nat := 4983230072969 + 3 ^ 40 * 718236 * 2
def baseEnd_718236 : Nat := 368800291362757132046899

theorem tailTrace_718236 : CollatzResearch.WordTrace tailWord_718236 prefixEnd_718236 368800291362757132046899 := by
  unfold tailWord_718236
  simp only [CollatzResearch.WordTrace]
  refine ⟨13098109512980555894027281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17464146017307407858703041 13098109512980555894027281)
  ·
    refine ⟨9823582134735416920520461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13098109512980555894027281 9823582134735416920520461)
    ·
      refine ⟨3683843300525781345195173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9823582134735416920520461 3683843300525781345195173)
      ·
        refine ⟨690720618848584002224095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3683843300525781345195173 690720618848584002224095)
        ·
          refine ⟨1036080928272876003336143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 690720618848584002224095 1036080928272876003336143)
          ·
            refine ⟨1554121392409314005004215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036080928272876003336143 1554121392409314005004215)
            ·
              refine ⟨2331182088613971007506323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1554121392409314005004215 2331182088613971007506323)
              ·
                refine ⟨3496773132920956511259485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331182088613971007506323 3496773132920956511259485)
                ·
                  refine ⟨1311289924845358691722307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3496773132920956511259485 1311289924845358691722307)
                  ·
                    refine ⟨1966934887268038037583461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1311289924845358691722307 1966934887268038037583461)
                    ·
                      refine ⟨368800291362757132046899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1966934887268038037583461 368800291362757132046899)
                      ·
                        rfl

theorem cell23_718236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_718236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718236 prefixEnd_718236 := by exact prefixLift 718236
  have htrace : WordTrace (prefixWord ++ tailWord_718236) baseStart_718236 baseEnd_718236 := by
    simpa [prefixWord, tailWord_718236, baseEnd_718236] using wordTrace_append hprefix tailTrace_718236
  have hstable : (prefixWord ++ tailWord_718236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718236).length < 2 ^ (prefixWord ++ tailWord_718236).sum := by decide
  have hdescent : baseEnd_718236 < baseStart_718236 := by decide
  rcases family_descends (prefixWord ++ tailWord_718236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718239 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 3]
def baseStart_718239 : Nat := 118140960795 + 718239 * 2 ^ 59
def prefixEnd_718239 : Nat := 4983230072969 + 3 ^ 40 * 718239 * 2
def baseEnd_718239 : Nat := 368801831804720620309385

theorem tailTrace_718239 : CollatzResearch.WordTrace tailWord_718239 prefixEnd_718239 368801831804720620309385 := by
  unfold tailWord_718239
  simp only [CollatzResearch.WordTrace]
  refine ⟨26196328444950243300413771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17464218963300162200275847 26196328444950243300413771)
  ·
    refine ⟨39294492667425364950620657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26196328444950243300413771 39294492667425364950620657)
    ·
      refine ⟨29470869500569023712965493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39294492667425364950620657 29470869500569023712965493)
      ·
        refine ⟨2762894015678345973090515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29470869500569023712965493 2762894015678345973090515)
        ·
          refine ⟨4144341023517518959635773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2762894015678345973090515 4144341023517518959635773)
          ·
            refine ⟨1554127883819069609863415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4144341023517518959635773 1554127883819069609863415)
            ·
              refine ⟨2331191825728604414795123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1554127883819069609863415 2331191825728604414795123)
              ·
                refine ⟨3496787738592906622192685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331191825728604414795123 3496787738592906622192685)
                ·
                  refine ⟨1311295401972339983322257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3496787738592906622192685 1311295401972339983322257)
                  ·
                    refine ⟨983471551479254987491693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1311295401972339983322257 983471551479254987491693)
                    ·
                      refine ⟨368801831804720620309385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 983471551479254987491693 368801831804720620309385)
                      ·
                        rfl

theorem cell23_718239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_718239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718239 prefixEnd_718239 := by exact prefixLift 718239
  have htrace : WordTrace (prefixWord ++ tailWord_718239) baseStart_718239 baseEnd_718239 := by
    simpa [prefixWord, tailWord_718239, baseEnd_718239] using wordTrace_append hprefix tailTrace_718239
  have hstable : (prefixWord ++ tailWord_718239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718239).length < 2 ^ (prefixWord ++ tailWord_718239).sum := by decide
  have hdescent : baseEnd_718239 < baseStart_718239 := by decide
  rcases family_descends (prefixWord ++ tailWord_718239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718242 : List Nat := [3, 3, 1, 2, 1, 2, 2, 9]
def baseStart_718242 : Nat := 118140960795 + 718242 * 2 ^ 59
def prefixEnd_718242 : Nat := 4983230072969 + 3 ^ 40 * 718242 * 2
def baseEnd_718242 : Nat := 13659384157284596613773

theorem tailTrace_718242 : CollatzResearch.WordTrace tailWord_718242 prefixEnd_718242 13659384157284596613773 := by
  unfold tailWord_718242
  simp only [CollatzResearch.WordTrace]
  refine ⟨6549109465984843703193245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17464291909292916541848653 6549109465984843703193245)
  ·
    refine ⟨2455916049744316388697467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6549109465984843703193245 2455916049744316388697467)
    ·
      refine ⟨3683874074616474583046201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2455916049744316388697467 3683874074616474583046201)
      ·
        refine ⟨2762905555962355937284651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3683874074616474583046201 2762905555962355937284651)
        ·
          refine ⟨4144358333943533905926977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2762905555962355937284651 4144358333943533905926977)
          ·
            refine ⟨3108268750457650429445233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4144358333943533905926977 3108268750457650429445233)
            ·
              refine ⟨2331201562843237822083925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3108268750457650429445233 2331201562843237822083925)
              ·
                refine ⟨13659384157284596613773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2331201562843237822083925 13659384157284596613773)
                ·
                  rfl

theorem cell23_718242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 9].length) (baseStart_718242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718242 prefixEnd_718242 := by exact prefixLift 718242
  have htrace : WordTrace (prefixWord ++ tailWord_718242) baseStart_718242 baseEnd_718242 := by
    simpa [prefixWord, tailWord_718242, baseEnd_718242] using wordTrace_append hprefix tailTrace_718242
  have hstable : (prefixWord ++ tailWord_718242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718242).length < 2 ^ (prefixWord ++ tailWord_718242).sum := by decide
  have hdescent : baseEnd_718242 < baseStart_718242 := by decide
  rcases family_descends (prefixWord ++ tailWord_718242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718252 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 3]
def baseStart_718252 : Nat := 118140960795 + 718252 * 2 ^ 59
def prefixEnd_718252 : Nat := 4983230072969 + 3 ^ 40 * 718252 * 2
def baseEnd_718252 : Nat := 368808507053229069446825

theorem tailTrace_718252 : CollatzResearch.WordTrace tailWord_718252 prefixEnd_718252 368808507053229069446825 := by
  unfold tailWord_718252
  simp only [CollatzResearch.WordTrace]
  refine ⟨13098401296951573260318505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17464535062602097680424673 13098401296951573260318505)
  ·
    refine ⟨9823800972713679945238879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13098401296951573260318505 9823800972713679945238879)
    ·
      refine ⟨14735701459070519917858319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9823800972713679945238879 14735701459070519917858319)
      ·
        refine ⟨22103552188605779876787479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14735701459070519917858319 22103552188605779876787479)
        ·
          refine ⟨33155328282908669815181219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22103552188605779876787479 33155328282908669815181219)
          ·
            refine ⟨49732992424363004722771829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33155328282908669815181219 49732992424363004722771829)
            ·
              refine ⟨4662468039784031692759859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49732992424363004722771829 4662468039784031692759859)
              ·
                refine ⟨6993702059676047539139789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4662468039784031692759859 6993702059676047539139789)
                ·
                  refine ⟨2622638272378517827177421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6993702059676047539139789 2622638272378517827177421)
                  ·
                    refine ⟨983489352141944185191533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2622638272378517827177421 983489352141944185191533)
                    ·
                      refine ⟨368808507053229069446825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 983489352141944185191533 368808507053229069446825)
                      ·
                        rfl

theorem cell23_718252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_718252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718252 prefixEnd_718252 := by exact prefixLift 718252
  have htrace : WordTrace (prefixWord ++ tailWord_718252) baseStart_718252 baseEnd_718252 := by
    simpa [prefixWord, tailWord_718252, baseEnd_718252] using wordTrace_append hprefix tailTrace_718252
  have hstable : (prefixWord ++ tailWord_718252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718252).length < 2 ^ (prefixWord ++ tailWord_718252).sum := by decide
  have hdescent : baseEnd_718252 < baseStart_718252 := by decide
  rcases family_descends (prefixWord ++ tailWord_718252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718253 : List Nat := [1, 5, 2, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_718253 : Nat := 118140960795 + 718253 * 2 ^ 59
def prefixEnd_718253 : Nat := 4983230072969 + 3 ^ 40 * 718253 * 2
def baseEnd_718253 : Nat := 368809020533883565534321

theorem tailTrace_718253 : CollatzResearch.WordTrace tailWord_718253 prefixEnd_718253 368809020533883565534321 := by
  unfold tailWord_718253
  simp only [CollatzResearch.WordTrace]
  refine ⟨26196839066899523691423413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17464559377933015794282275 26196839066899523691423413)
  ·
    refine ⟨2455953662521830346070945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26196839066899523691423413 2455953662521830346070945)
    ·
      refine ⟨1841965246891372759553209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2455953662521830346070945 1841965246891372759553209)
      ·
        refine ⟨1381473935168529569664907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1841965246891372759553209 1381473935168529569664907)
        ·
          refine ⟨2072210902752794354497361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1381473935168529569664907 2072210902752794354497361)
          ·
            refine ⟨1554158177064595765873021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2072210902752794354497361 1554158177064595765873021)
            ·
              refine ⟨582809316399223412202383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1554158177064595765873021 582809316399223412202383)
              ·
                refine ⟨874213974598835118303575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582809316399223412202383 874213974598835118303575)
                ·
                  refine ⟨1311320961898252677455363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 874213974598835118303575 1311320961898252677455363)
                  ·
                    refine ⟨1966981442847379016183045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1311320961898252677455363 1966981442847379016183045)
                    ·
                      refine ⟨368809020533883565534321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1966981442847379016183045 368809020533883565534321)
                      ·
                        rfl

theorem cell23_718253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_718253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718253 prefixEnd_718253 := by exact prefixLift 718253
  have htrace : WordTrace (prefixWord ++ tailWord_718253) baseStart_718253 baseEnd_718253 := by
    simpa [prefixWord, tailWord_718253, baseEnd_718253] using wordTrace_append hprefix tailTrace_718253
  have hstable : (prefixWord ++ tailWord_718253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718253).length < 2 ^ (prefixWord ++ tailWord_718253).sum := by decide
  have hdescent : baseEnd_718253 < baseStart_718253 := by decide
  rcases family_descends (prefixWord ++ tailWord_718253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718255 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 4, 7]
def baseStart_718255 : Nat := 118140960795 + 718255 * 2 ^ 59
def prefixEnd_718255 : Nat := 4983230072969 + 3 ^ 40 * 718255 * 2
def baseEnd_718255 : Nat := 122936682498397519236437

theorem tailTrace_718255 : CollatzResearch.WordTrace tailWord_718255 prefixEnd_718255 122936682498397519236437 := by
  unfold tailWord_718255
  simp only [CollatzResearch.WordTrace]
  refine ⟨26196912012892278032996219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17464608008594852021997479 26196912012892278032996219)
  ·
    refine ⟨39295368019338417049494329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26196912012892278032996219 39295368019338417049494329)
    ·
      refine ⟨29471526014503812787120747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39295368019338417049494329 29471526014503812787120747)
      ·
        refine ⟨44207289021755719180681121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29471526014503812787120747 44207289021755719180681121)
        ·
          refine ⟨33155466766316789385510841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44207289021755719180681121 33155466766316789385510841)
          ·
            refine ⟨24866600074737592039133131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33155466766316789385510841 24866600074737592039133131)
            ·
              refine ⟨37299900112106388058699697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24866600074737592039133131 37299900112106388058699697)
              ·
                refine ⟨27974925084079791044024773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37299900112106388058699697 27974925084079791044024773)
                ·
                  refine ⟨5245298453264960820754645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27974925084079791044024773 5245298453264960820754645)
                  ·
                    refine ⟨122936682498397519236437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5245298453264960820754645 122936682498397519236437)
                    ·
                      rfl

theorem cell23_718255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 7].length) (baseStart_718255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718255 prefixEnd_718255 := by exact prefixLift 718255
  have htrace : WordTrace (prefixWord ++ tailWord_718255) baseStart_718255 baseEnd_718255 := by
    simpa [prefixWord, tailWord_718255, baseEnd_718255] using wordTrace_append hprefix tailTrace_718255
  have hstable : (prefixWord ++ tailWord_718255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718255).length < 2 ^ (prefixWord ++ tailWord_718255).sum := by decide
  have hdescent : baseEnd_718255 < baseStart_718255 := by decide
  rcases family_descends (prefixWord ++ tailWord_718255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718279 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 5, 3, 2]
def baseStart_718279 : Nat := 118140960795 + 718279 * 2 ^ 59
def prefixEnd_718279 : Nat := 4983230072969 + 3 ^ 40 * 718279 * 2
def baseEnd_718279 : Nat := 368822371030900463809201

theorem tailTrace_718279 : CollatzResearch.WordTrace tailWord_718279 prefixEnd_718279 368822371030900463809201 := by
  unfold tailWord_718279
  simp only [CollatzResearch.WordTrace]
  refine ⟨26197787364805330131869891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17465191576536886754579927 26197787364805330131869891)
  ·
    refine ⟨39296681047207995197804837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26197787364805330131869891 39296681047207995197804837)
    ·
      refine ⟨7368127696351499099588407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39296681047207995197804837 7368127696351499099588407)
      ·
        refine ⟨11052191544527248649382611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7368127696351499099588407 11052191544527248649382611)
        ·
          refine ⟨16578287316790872974073917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11052191544527248649382611 16578287316790872974073917)
          ·
            refine ⟨6216857743796577365277719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16578287316790872974073917 6216857743796577365277719)
            ·
              refine ⟨9325286615694866047916579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6216857743796577365277719 9325286615694866047916579)
              ·
                refine ⟨13987929923542299071874869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9325286615694866047916579 13987929923542299071874869)
                ·
                  refine ⟨1311368430332090537988269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13987929923542299071874869 1311368430332090537988269)
                  ·
                    refine ⟨491763161374533951745601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1311368430332090537988269 491763161374533951745601)
                    ·
                      refine ⟨368822371030900463809201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 491763161374533951745601 368822371030900463809201)
                      ·
                        rfl

theorem cell23_718279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_718279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718279 prefixEnd_718279 := by exact prefixLift 718279
  have htrace : WordTrace (prefixWord ++ tailWord_718279) baseStart_718279 baseEnd_718279 := by
    simpa [prefixWord, tailWord_718279, baseEnd_718279] using wordTrace_append hprefix tailTrace_718279
  have hstable : (prefixWord ++ tailWord_718279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718279).length < 2 ^ (prefixWord ++ tailWord_718279).sum := by decide
  have hdescent : baseEnd_718279 < baseStart_718279 := by decide
  rcases family_descends (prefixWord ++ tailWord_718279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718286 : List Nat := [4, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3]
def baseStart_718286 : Nat := 118140960795 + 718286 * 2 ^ 59
def prefixEnd_718286 : Nat := 4983230072969 + 3 ^ 40 * 718286 * 2
def baseEnd_718286 : Nat := 368825965395481936421669

theorem tailTrace_718286 : CollatzResearch.WordTrace tailWord_718286 prefixEnd_718286 368825965395481936421669 := by
  unfold tailWord_718286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3274755334472496290921839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17465361783853313551583141 3274755334472496290921839)
  ·
    refine ⟨4912133001708744436382759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3274755334472496290921839 4912133001708744436382759)
    ·
      refine ⟨7368199502563116654574139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4912133001708744436382759 7368199502563116654574139)
      ·
        refine ⟨11052299253844674981861209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7368199502563116654574139 11052299253844674981861209)
        ·
          refine ⟨8289224440383506236395907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11052299253844674981861209 8289224440383506236395907)
          ·
            refine ⟨12433836660575259354593861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8289224440383506236395907 12433836660575259354593861)
            ·
              refine ⟨2331344373857861128986349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12433836660575259354593861 2331344373857861128986349)
              ·
                refine ⟨874254140196697923369881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2331344373857861128986349 874254140196697923369881)
                ·
                  refine ⟨655690605147523442527411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 874254140196697923369881 655690605147523442527411)
                  ·
                    refine ⟨983535907721285163791117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 655690605147523442527411 983535907721285163791117)
                    ·
                      refine ⟨368825965395481936421669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 983535907721285163791117 368825965395481936421669)
                      ·
                        rfl

theorem cell23_718286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_718286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718286 prefixEnd_718286 := by exact prefixLift 718286
  have htrace : WordTrace (prefixWord ++ tailWord_718286) baseStart_718286 baseEnd_718286 := by
    simpa [prefixWord, tailWord_718286, baseEnd_718286] using wordTrace_append hprefix tailTrace_718286
  have hstable : (prefixWord ++ tailWord_718286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718286).length < 2 ^ (prefixWord ++ tailWord_718286).sum := by decide
  have hdescent : baseEnd_718286 < baseStart_718286 := by decide
  rcases family_descends (prefixWord ++ tailWord_718286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718312 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_718312 : Nat := 118140960795 + 718312 * 2 ^ 59
def prefixEnd_718312 : Nat := 4983230072969 + 3 ^ 40 * 718312 * 2
def baseEnd_718312 : Nat := 368839315892498834696549

theorem tailTrace_718312 : CollatzResearch.WordTrace tailWord_718312 prefixEnd_718312 368839315892498834696549 := by
  unfold tailWord_718312
  simp only [CollatzResearch.WordTrace]
  refine ⟨13099495486842888383910595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17465993982457184511880793 13099495486842888383910595)
  ·
    refine ⟨19649243230264332575865893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13099495486842888383910595 19649243230264332575865893)
    ·
      refine ⟨3684233105674562357974855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19649243230264332575865893 3684233105674562357974855)
      ·
        refine ⟨5526349658511843536962283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3684233105674562357974855 5526349658511843536962283)
        ·
          refine ⟨8289524487767765305443425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5526349658511843536962283 8289524487767765305443425)
          ·
            refine ⟨6217143365825823979082569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8289524487767765305443425 6217143365825823979082569)
            ·
              refine ⟨4662857524369367984311927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6217143365825823979082569 4662857524369367984311927)
              ·
                refine ⟨6994286286554051976467891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4662857524369367984311927 6994286286554051976467891)
                ·
                  refine ⟨10491429429831077964701837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6994286286554051976467891 10491429429831077964701837)
                  ·
                    refine ⟨3934286036186654236763189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10491429429831077964701837 3934286036186654236763189)
                    ·
                      refine ⟨368839315892498834696549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3934286036186654236763189 368839315892498834696549)
                      ·
                        rfl

theorem cell23_718312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_718312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718312 prefixEnd_718312 := by exact prefixLift 718312
  have htrace : WordTrace (prefixWord ++ tailWord_718312) baseStart_718312 baseEnd_718312 := by
    simpa [prefixWord, tailWord_718312, baseEnd_718312] using wordTrace_append hprefix tailTrace_718312
  have hstable : (prefixWord ++ tailWord_718312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718312).length < 2 ^ (prefixWord ++ tailWord_718312).sum := by decide
  have hdescent : baseEnd_718312 < baseStart_718312 := by decide
  rcases family_descends (prefixWord ++ tailWord_718312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718332 : List Nat := [2, 2, 2, 1, 2, 1, 3, 3, 7]
def baseStart_718332 : Nat := 118140960795 + 718332 * 2 ^ 59
def prefixEnd_718332 : Nat := 4983230072969 + 3 ^ 40 * 718332 * 2
def baseEnd_718332 : Nat := 40983287278398750716273

theorem tailTrace_718332 : CollatzResearch.WordTrace tailWord_718332 prefixEnd_718332 40983287278398750716273 := by
  unfold tailWord_718332
  simp only [CollatzResearch.WordTrace]
  refine ⟨13099860216806660091774625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17466480289075546789032833 13099860216806660091774625)
  ·
    refine ⟨9824895162604995068830969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13099860216806660091774625 9824895162604995068830969)
    ·
      refine ⟨7368671371953746301623227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9824895162604995068830969 7368671371953746301623227)
      ·
        refine ⟨11053007057930619452434841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7368671371953746301623227 11053007057930619452434841)
        ·
          refine ⟨8289755293447964589326131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11053007057930619452434841 8289755293447964589326131)
          ·
            refine ⟨12434632940171946883989197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8289755293447964589326131 12434632940171946883989197)
            ·
              refine ⟨4662987352564480081495949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12434632940171946883989197 4662987352564480081495949)
              ·
                refine ⟨1748620257211680030560981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4662987352564480081495949 1748620257211680030560981)
                ·
                  refine ⟨40983287278398750716273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1748620257211680030560981 40983287278398750716273)
                  ·
                    rfl

theorem cell23_718332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 7].length) (baseStart_718332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718332 prefixEnd_718332 := by exact prefixLift 718332
  have htrace : WordTrace (prefixWord ++ tailWord_718332) baseStart_718332 baseEnd_718332 := by
    simpa [prefixWord, tailWord_718332, baseEnd_718332] using wordTrace_append hprefix tailTrace_718332
  have hstable : (prefixWord ++ tailWord_718332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718332).length < 2 ^ (prefixWord ++ tailWord_718332).sum := by decide
  have hdescent : baseEnd_718332 < baseStart_718332 := by decide
  rcases family_descends (prefixWord ++ tailWord_718332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718343 : List Nat := [1, 1, 4, 3, 2, 3, 1, 1, 1, 4, 2]
def baseStart_718343 : Nat := 118140960795 + 718343 * 2 ^ 59
def prefixEnd_718343 : Nat := 4983230072969 + 3 ^ 40 * 718343 * 2
def baseEnd_718343 : Nat := 368855233792788213408907

theorem tailTrace_718343 : CollatzResearch.WordTrace tailWord_718343 prefixEnd_718343 368855233792788213408907 := by
  unfold tailWord_718343
  simp only [CollatzResearch.WordTrace]
  refine ⟨26200121636573469062199683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17466747757715646041466455 26200121636573469062199683)
  ·
    refine ⟨39300182454860203593299525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26200121636573469062199683 39300182454860203593299525)
    ·
      refine ⟨7368784210286288173743661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39300182454860203593299525 7368784210286288173743661)
      ·
        refine ⟨2763294078857358065153873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7368784210286288173743661 2763294078857358065153873)
        ·
          refine ⟨2072470559143018548865405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2763294078857358065153873 2072470559143018548865405)
          ·
            refine ⟨777176459678631955824527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2072470559143018548865405 777176459678631955824527)
            ·
              refine ⟨1165764689517947933736791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777176459678631955824527 1165764689517947933736791)
              ·
                refine ⟨1748647034276921900605187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165764689517947933736791 1748647034276921900605187)
                ·
                  refine ⟨2622970551415382850907781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1748647034276921900605187 2622970551415382850907781)
                  ·
                    refine ⟨491806978390384284545209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2622970551415382850907781 491806978390384284545209)
                    ·
                      refine ⟨368855233792788213408907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 491806978390384284545209 368855233792788213408907)
                      ·
                        rfl

theorem cell23_718343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_718343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718343 prefixEnd_718343 := by exact prefixLift 718343
  have htrace : WordTrace (prefixWord ++ tailWord_718343) baseStart_718343 baseEnd_718343 := by
    simpa [prefixWord, tailWord_718343, baseEnd_718343] using wordTrace_append hprefix tailTrace_718343
  have hstable : (prefixWord ++ tailWord_718343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718343).length < 2 ^ (prefixWord ++ tailWord_718343).sum := by decide
  have hdescent : baseEnd_718343 < baseStart_718343 := by decide
  rcases family_descends (prefixWord ++ tailWord_718343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718389 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_718389 : Nat := 118140960795 + 718389 * 2 ^ 59
def prefixEnd_718389 : Nat := 4983230072969 + 3 ^ 40 * 718389 * 2
def baseEnd_718389 : Nat := 368878853902895033433695

theorem tailTrace_718389 : CollatzResearch.WordTrace tailWord_718389 prefixEnd_718389 368878853902895033433695 := by
  unfold tailWord_718389
  simp only [CollatzResearch.WordTrace]
  refine ⟨26201799394406818918374221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17467866262937879278916147 26201799394406818918374221)
  ·
    refine ⟨9825674772902557094390333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26201799394406818918374221 9825674772902557094390333)
    ·
      refine ⟨3684628039838458910396375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9825674772902557094390333 3684628039838458910396375)
      ·
        refine ⟨5526942059757688365594563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3684628039838458910396375 5526942059757688365594563)
        ·
          refine ⟨8290413089636532548391845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5526942059757688365594563 8290413089636532548391845)
          ·
            refine ⟨1554452454306849852823471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8290413089636532548391845 1554452454306849852823471)
            ·
              refine ⟨2331678681460274779235207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1554452454306849852823471 2331678681460274779235207)
              ·
                refine ⟨3497518022190412168852811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331678681460274779235207 3497518022190412168852811)
                ·
                  refine ⟨5246277033285618253279217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3497518022190412168852811 5246277033285618253279217)
                  ·
                    refine ⟨3934707774964213689959413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5246277033285618253279217 3934707774964213689959413)
                    ·
                      refine ⟨368878853902895033433695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3934707774964213689959413 368878853902895033433695)
                      ·
                        rfl

theorem cell23_718389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_718389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718389 prefixEnd_718389 := by exact prefixLift 718389
  have htrace : WordTrace (prefixWord ++ tailWord_718389) baseStart_718389 baseEnd_718389 := by
    simpa [prefixWord, tailWord_718389, baseEnd_718389] using wordTrace_append hprefix tailTrace_718389
  have hstable : (prefixWord ++ tailWord_718389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718389).length < 2 ^ (prefixWord ++ tailWord_718389).sum := by decide
  have hdescent : baseEnd_718389 < baseStart_718389 := by decide
  rcases family_descends (prefixWord ++ tailWord_718389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718409 : List Nat := [1, 2, 1, 1, 2, 2, 1, 6, 3, 4]
def baseStart_718409 : Nat := 118140960795 + 718409 * 2 ^ 59
def prefixEnd_718409 : Nat := 4983230072969 + 3 ^ 40 * 718409 * 2
def baseEnd_718409 : Nat := 122963041171994985061201

theorem tailTrace_718409 : CollatzResearch.WordTrace tailWord_718409 prefixEnd_718409 122963041171994985061201 := by
  unfold tailWord_718409
  simp only [CollatzResearch.WordTrace]
  refine ⟨26202528854334362334102281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17468352569556241556068187 26202528854334362334102281)
  ·
    refine ⟨19651896640750771750576711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26202528854334362334102281 19651896640750771750576711)
    ·
      refine ⟨29477844961126157625865067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19651896640750771750576711 29477844961126157625865067)
      ·
        refine ⟨44216767441689236438797601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29477844961126157625865067 44216767441689236438797601)
        ·
          refine ⟨33162575581266927329098201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44216767441689236438797601 33162575581266927329098201)
          ·
            refine ⟨24871931685950195496823651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33162575581266927329098201 24871931685950195496823651)
            ·
              refine ⟨37307897528925293245235477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24871931685950195496823651 37307897528925293245235477)
              ·
                refine ⟨1748807696668373120870413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37307897528925293245235477 1748807696668373120870413)
                ·
                  refine ⟨655802886250639920326405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1748807696668373120870413 655802886250639920326405)
                  ·
                    refine ⟨122963041171994985061201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 655802886250639920326405 122963041171994985061201)
                    ·
                      rfl

theorem cell23_718409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 4].length) (baseStart_718409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718409 prefixEnd_718409 := by exact prefixLift 718409
  have htrace : WordTrace (prefixWord ++ tailWord_718409) baseStart_718409 baseEnd_718409 := by
    simpa [prefixWord, tailWord_718409, baseEnd_718409] using wordTrace_append hprefix tailTrace_718409
  have hstable : (prefixWord ++ tailWord_718409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718409).length < 2 ^ (prefixWord ++ tailWord_718409).sum := by decide
  have hdescent : baseEnd_718409 < baseStart_718409 := by decide
  rcases family_descends (prefixWord ++ tailWord_718409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718413 : List Nat := [1, 6, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_718413 : Nat := 118140960795 + 718413 * 2 ^ 59
def prefixEnd_718413 : Nat := 4983230072969 + 3 ^ 40 * 718413 * 2
def baseEnd_718413 : Nat := 122963725812867646511195

theorem tailTrace_718413 : CollatzResearch.WordTrace tailWord_718413 prefixEnd_718413 122963725812867646511195 := by
  unfold tailWord_718413
  simp only [CollatzResearch.WordTrace]
  refine ⟨26202674746319871017247893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17468449830879914011498595 26202674746319871017247893)
  ·
    refine ⟨1228250378733743953933495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26202674746319871017247893 1228250378733743953933495)
    ·
      refine ⟨1842375568100615930900243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1228250378733743953933495 1842375568100615930900243)
      ·
        refine ⟨2763563352150923896350365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1842375568100615930900243 2763563352150923896350365)
        ·
          refine ⟨1036336257056596461131387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2763563352150923896350365 1036336257056596461131387)
          ·
            refine ⟨1554504385584894691697081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036336257056596461131387 1554504385584894691697081)
            ·
              refine ⟨1165878289188671018772811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1554504385584894691697081 1165878289188671018772811)
              ·
                refine ⟨1748817433783006528159217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165878289188671018772811 1748817433783006528159217)
                ·
                  refine ⟨1311613075337254896119413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1748817433783006528159217 1311613075337254896119413)
                  ·
                    refine ⟨122963725812867646511195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1311613075337254896119413 122963725812867646511195)
                    ·
                      rfl

theorem cell23_718413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_718413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718413 prefixEnd_718413 := by exact prefixLift 718413
  have htrace : WordTrace (prefixWord ++ tailWord_718413) baseStart_718413 baseEnd_718413 := by
    simpa [prefixWord, tailWord_718413, baseEnd_718413] using wordTrace_append hprefix tailTrace_718413
  have hstable : (prefixWord ++ tailWord_718413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718413).length < 2 ^ (prefixWord ++ tailWord_718413).sum := by decide
  have hdescent : baseEnd_718413 < baseStart_718413 := by decide
  rcases family_descends (prefixWord ++ tailWord_718413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718436 : List Nat := [2, 3, 1, 1, 2, 3, 2, 2, 2, 2, 3]
def baseStart_718436 : Nat := 118140960795 + 718436 * 2 ^ 59
def prefixEnd_718436 : Nat := 4983230072969 + 3 ^ 40 * 718436 * 2
def baseEnd_718436 : Nat := 368902987493656349545979

theorem tailTrace_718436 : CollatzResearch.WordTrace tailWord_718436 prefixEnd_718436 368902987493656349545979 := by
  unfold tailWord_718436
  simp only [CollatzResearch.WordTrace]
  refine ⟨13101756812618272972667581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17469009083491030630223441 13101756812618272972667581)
  ·
    refine ⟨4913158804731852364750343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13101756812618272972667581 4913158804731852364750343)
    ·
      refine ⟨7369738207097778547125515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4913158804731852364750343 7369738207097778547125515)
      ·
        refine ⟨11054607310646667820688273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7369738207097778547125515 11054607310646667820688273)
        ·
          refine ⟨8290955482985000865516205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11054607310646667820688273 8290955482985000865516205)
          ·
            refine ⟨3109108306119375324568577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8290955482985000865516205 3109108306119375324568577)
            ·
              refine ⟨2331831229589531493426433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3109108306119375324568577 2331831229589531493426433)
              ·
                refine ⟨1748873422192148620069825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2331831229589531493426433 1748873422192148620069825)
                ·
                  refine ⟨1311655066644111465052369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1748873422192148620069825 1311655066644111465052369)
                  ·
                    refine ⟨983741299983083598789277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1311655066644111465052369 983741299983083598789277)
                    ·
                      refine ⟨368902987493656349545979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 983741299983083598789277 368902987493656349545979)
                      ·
                        rfl

theorem cell23_718436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_718436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718436 prefixEnd_718436 := by exact prefixLift 718436
  have htrace : WordTrace (prefixWord ++ tailWord_718436) baseStart_718436 baseEnd_718436 := by
    simpa [prefixWord, tailWord_718436, baseEnd_718436] using wordTrace_append hprefix tailTrace_718436
  have hstable : (prefixWord ++ tailWord_718436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718436).length < 2 ^ (prefixWord ++ tailWord_718436).sum := by decide
  have hdescent : baseEnd_718436 < baseStart_718436 := by decide
  rcases family_descends (prefixWord ++ tailWord_718436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718439 : List Nat := [1, 1, 5, 1, 1, 1, 3, 4, 6]
def baseStart_718439 : Nat := 118140960795 + 718439 * 2 ^ 59
def prefixEnd_718439 : Nat := 4983230072969 + 3 ^ 40 * 718439 * 2
def baseEnd_718439 : Nat := 40989391992846648645385

theorem tailTrace_718439 : CollatzResearch.WordTrace tailWord_718439 prefixEnd_718439 40989391992846648645385 := by
  unfold tailWord_718439
  simp only [CollatzResearch.WordTrace]
  refine ⟨26203623044225677457694371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17469082029483784971796247 26203623044225677457694371)
  ·
    refine ⟨39305434566338516186541557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26203623044225677457694371 39305434566338516186541557)
    ·
      refine ⟨3684884490594235892488271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39305434566338516186541557 3684884490594235892488271)
      ·
        refine ⟨5527326735891353838732407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3684884490594235892488271 5527326735891353838732407)
        ·
          refine ⟨8290990103837030758098611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5527326735891353838732407 8290990103837030758098611)
          ·
            refine ⟨12436485155755546137147917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8290990103837030758098611 12436485155755546137147917)
            ·
              refine ⟨4663681933408329801430469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12436485155755546137147917 4663681933408329801430469)
              ·
                refine ⟨874440362514061837768213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4663681933408329801430469 874440362514061837768213)
                ·
                  refine ⟨40989391992846648645385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 874440362514061837768213 40989391992846648645385)
                  ·
                    rfl

theorem cell23_718439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 6].length) (baseStart_718439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718439 prefixEnd_718439 := by exact prefixLift 718439
  have htrace : WordTrace (prefixWord ++ tailWord_718439) baseStart_718439 baseEnd_718439 := by
    simpa [prefixWord, tailWord_718439, baseEnd_718439] using wordTrace_append hprefix tailTrace_718439
  have hstable : (prefixWord ++ tailWord_718439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718439).length < 2 ^ (prefixWord ++ tailWord_718439).sum := by decide
  have hdescent : baseEnd_718439 < baseStart_718439 := by decide
  rcases family_descends (prefixWord ++ tailWord_718439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718469 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 3, 5]
def baseStart_718469 : Nat := 118140960795 + 718469 * 2 ^ 59
def prefixEnd_718469 : Nat := 4983230072969 + 3 ^ 40 * 718469 * 2
def baseEnd_718469 : Nat := 122973310785084906811109

theorem tailTrace_718469 : CollatzResearch.WordTrace tailWord_718469 prefixEnd_718469 122973310785084906811109 := by
  unfold tailWord_718469
  simp only [CollatzResearch.WordTrace]
  refine ⟨26204717234116992581286461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17469811489411328387524307 26204717234116992581286461)
  ·
    refine ⟨9826768962793872217982423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26204717234116992581286461 9826768962793872217982423)
    ·
      refine ⟨14740153444190808326973635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9826768962793872217982423 14740153444190808326973635)
      ·
        refine ⟨22110230166286212490460453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14740153444190808326973635 22110230166286212490460453)
        ·
          refine ⟨4145668156178664841961335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22110230166286212490460453 4145668156178664841961335)
          ·
            refine ⟨6218502234267997262942003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4145668156178664841961335 6218502234267997262942003)
            ·
              refine ⟨9327753351401995894413005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6218502234267997262942003 9327753351401995894413005)
              ·
                refine ⟨3497907506775748460404877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9327753351401995894413005 3497907506775748460404877)
                ·
                  refine ⟨1311715315040905672651829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3497907506775748460404877 1311715315040905672651829)
                  ·
                    refine ⟨122973310785084906811109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1311715315040905672651829 122973310785084906811109)
                    ·
                      rfl

theorem cell23_718469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_718469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718469 prefixEnd_718469 := by exact prefixLift 718469
  have htrace : WordTrace (prefixWord ++ tailWord_718469) baseStart_718469 baseEnd_718469 := by
    simpa [prefixWord, tailWord_718469, baseEnd_718469] using wordTrace_append hprefix tailTrace_718469
  have hstable : (prefixWord ++ tailWord_718469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718469).length < 2 ^ (prefixWord ++ tailWord_718469).sum := by decide
  have hdescent : baseEnd_718469 < baseStart_718469 := by decide
  rcases family_descends (prefixWord ++ tailWord_718469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718476 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 1, 5, 2]
def baseStart_718476 : Nat := 118140960795 + 718476 * 2 ^ 59
def prefixEnd_718476 : Nat := 4983230072969 + 3 ^ 40 * 718476 * 2
def baseEnd_718476 : Nat := 368923526719836193045795

theorem tailTrace_718476 : CollatzResearch.WordTrace tailWord_718476 prefixEnd_718476 368923526719836193045795 := by
  unfold tailWord_718476
  simp only [CollatzResearch.WordTrace]
  refine ⟨13102486272545816388395641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17469981696727755184527521 13102486272545816388395641)
  ·
    refine ⟨9826864704409362291296731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13102486272545816388395641 9826864704409362291296731)
    ·
      refine ⟨14740297056614043436945097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9826864704409362291296731 14740297056614043436945097)
      ·
        refine ⟨11055222792460532577708823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14740297056614043436945097 11055222792460532577708823)
        ·
          refine ⟨16582834188690798866563235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11055222792460532577708823 16582834188690798866563235)
          ·
            refine ⟨24874251283036198299844853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16582834188690798866563235 24874251283036198299844853)
            ·
              refine ⟨2331961057784643590610455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24874251283036198299844853 2331961057784643590610455)
              ·
                refine ⟨3497941586676965385915683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331961057784643590610455 3497941586676965385915683)
                ·
                  refine ⟨5246912380015448078873525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3497941586676965385915683 5246912380015448078873525)
                  ·
                    refine ⟨491898035626448257394393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5246912380015448078873525 491898035626448257394393)
                    ·
                      refine ⟨368923526719836193045795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 491898035626448257394393 368923526719836193045795)
                      ·
                        rfl

theorem cell23_718476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_718476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718476 prefixEnd_718476 := by exact prefixLift 718476
  have htrace : WordTrace (prefixWord ++ tailWord_718476) baseStart_718476 baseEnd_718476 := by
    simpa [prefixWord, tailWord_718476, baseEnd_718476] using wordTrace_append hprefix tailTrace_718476
  have hstable : (prefixWord ++ tailWord_718476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718476).length < 2 ^ (prefixWord ++ tailWord_718476).sum := by decide
  have hdescent : baseEnd_718476 < baseStart_718476 := by decide
  rcases family_descends (prefixWord ++ tailWord_718476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718489 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 5, 1, 4]
def baseStart_718489 : Nat := 118140960795 + 718489 * 2 ^ 59
def prefixEnd_718489 : Nat := 4983230072969 + 3 ^ 40 * 718489 * 2
def baseEnd_718489 : Nat := 368930201968344642183235

theorem tailTrace_718489 : CollatzResearch.WordTrace tailWord_718489 prefixEnd_718489 368930201968344642183235 := by
  unfold tailWord_718489
  simp only [CollatzResearch.WordTrace]
  refine ⟨26205446694044535997014521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17470297796029690664676347 26205446694044535997014521)
  ·
    refine ⟨19654085020533401997760891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26205446694044535997014521 19654085020533401997760891)
    ·
      refine ⟨29481127530800102996641337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19654085020533401997760891 29481127530800102996641337)
      ·
        refine ⟨22110845648100077247481003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29481127530800102996641337 22110845648100077247481003)
        ·
          refine ⟨33166268472150115871221505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22110845648100077247481003 33166268472150115871221505)
          ·
            refine ⟨24874701354112586903416129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33166268472150115871221505 24874701354112586903416129)
            ·
              refine ⟨18656026015584440177562097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24874701354112586903416129 18656026015584440177562097)
              ·
                refine ⟨13992019511688330133171573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18656026015584440177562097 13992019511688330133171573)
                ·
                  refine ⟨1311751829220780949984835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13992019511688330133171573 1311751829220780949984835)
                  ·
                    refine ⟨1967627743831171424977253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1311751829220780949984835 1967627743831171424977253)
                    ·
                      refine ⟨368930201968344642183235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1967627743831171424977253 368930201968344642183235)
                      ·
                        rfl

theorem cell23_718489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_718489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718489 prefixEnd_718489 := by exact prefixLift 718489
  have htrace : WordTrace (prefixWord ++ tailWord_718489) baseStart_718489 baseEnd_718489 := by
    simpa [prefixWord, tailWord_718489, baseEnd_718489] using wordTrace_append hprefix tailTrace_718489
  have hstable : (prefixWord ++ tailWord_718489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718489).length < 2 ^ (prefixWord ++ tailWord_718489).sum := by decide
  have hdescent : baseEnd_718489 < baseStart_718489 := by decide
  rcases family_descends (prefixWord ++ tailWord_718489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718500 : List Nat := [2, 3, 1, 2, 2, 2, 2, 4, 1, 1, 3]
def baseStart_718500 : Nat := 118140960795 + 718500 * 2 ^ 59
def prefixEnd_718500 : Nat := 4983230072969 + 3 ^ 40 * 718500 * 2
def baseEnd_718500 : Nat := 368935850255544099145685

theorem tailTrace_718500 : CollatzResearch.WordTrace tailWord_718500 prefixEnd_718500 368935850255544099145685 := by
  unfold tailWord_718500
  simp only [CollatzResearch.WordTrace]
  refine ⟨13102923948502342437832477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17470565264669789917109969 13102923948502342437832477)
  ·
    refine ⟨4913596480688378414187179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13102923948502342437832477 4913596480688378414187179)
    ·
      refine ⟨7370394721032567621280769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4913596480688378414187179 7370394721032567621280769)
      ·
        refine ⟨5527796040774425715960577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7370394721032567621280769 5527796040774425715960577)
        ·
          refine ⟨4145847030580819286970433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5527796040774425715960577 4145847030580819286970433)
          ·
            refine ⟨3109385272935614465227825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4145847030580819286970433 3109385272935614465227825)
            ·
              refine ⟨2332038954701710848920869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3109385272935614465227825 2332038954701710848920869)
              ·
                refine ⟨437257304006570784172663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2332038954701710848920869 437257304006570784172663)
                ·
                  refine ⟨655885956009856176258995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 437257304006570784172663 655885956009856176258995)
                  ·
                    refine ⟨983828934014784264388493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 655885956009856176258995 983828934014784264388493)
                    ·
                      refine ⟨368935850255544099145685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 983828934014784264388493 368935850255544099145685)
                      ·
                        rfl

theorem cell23_718500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_718500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718500 prefixEnd_718500 := by exact prefixLift 718500
  have htrace : WordTrace (prefixWord ++ tailWord_718500) baseStart_718500 baseEnd_718500 := by
    simpa [prefixWord, tailWord_718500, baseEnd_718500] using wordTrace_append hprefix tailTrace_718500
  have hstable : (prefixWord ++ tailWord_718500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718500).length < 2 ^ (prefixWord ++ tailWord_718500).sum := by decide
  have hdescent : baseEnd_718500 < baseStart_718500 := by decide
  rcases family_descends (prefixWord ++ tailWord_718500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718546 : List Nat := [3, 2, 2, 2, 2, 3, 9]
def baseStart_718546 : Nat := 118140960795 + 718546 * 2 ^ 59
def prefixEnd_718546 : Nat := 4983230072969 + 3 ^ 40 * 718546 * 2
def baseEnd_718546 : Nat := 4555055189699394063833

theorem tailTrace_718546 : CollatzResearch.WordTrace tailWord_718546 prefixEnd_718546 4555055189699394063833 := by
  unfold tailWord_718546
  simp only [CollatzResearch.WordTrace]
  refine ⟨6551881413709508682959873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17471683769892023154559661 6551881413709508682959873)
  ·
    refine ⟨4913911060282131512219905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6551881413709508682959873 4913911060282131512219905)
    ·
      refine ⟨3685433295211598634164929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4913911060282131512219905 3685433295211598634164929)
      ·
        refine ⟨2764074971408698975623697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3685433295211598634164929 2764074971408698975623697)
        ·
          refine ⟨2073056228556524231717773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2764074971408698975623697 2073056228556524231717773)
          ·
            refine ⟨777396085708696586894165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2073056228556524231717773 777396085708696586894165)
            ·
              refine ⟨4555055189699394063833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 777396085708696586894165 4555055189699394063833)
              ·
                rfl

theorem cell23_718546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 9].length) (baseStart_718546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718546 prefixEnd_718546 := by exact prefixLift 718546
  have htrace : WordTrace (prefixWord ++ tailWord_718546) baseStart_718546 baseEnd_718546 := by
    simpa [prefixWord, tailWord_718546, baseEnd_718546] using wordTrace_append hprefix tailTrace_718546
  have hstable : (prefixWord ++ tailWord_718546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718546).length < 2 ^ (prefixWord ++ tailWord_718546).sum := by decide
  have hdescent : baseEnd_718546 < baseStart_718546 := by decide
  rcases family_descends (prefixWord ++ tailWord_718546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718559 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 2, 7]
def baseStart_718559 : Nat := 118140960795 + 718559 * 2 ^ 59
def prefixEnd_718559 : Nat := 4983230072969 + 3 ^ 40 * 718559 * 2
def baseEnd_718559 : Nat := 122988715204719789435971

theorem tailTrace_718559 : CollatzResearch.WordTrace tailWord_718559 prefixEnd_718559 122988715204719789435971 := by
  unfold tailWord_718559
  simp only [CollatzResearch.WordTrace]
  refine ⟨26207999803790937952062731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17471999869193958634708487 26207999803790937952062731)
  ·
    refine ⟨39311999705686406928094097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26207999803790937952062731 39311999705686406928094097)
    ·
      refine ⟨29483999779264805196070573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39311999705686406928094097 29483999779264805196070573)
      ·
        refine ⟨11056499917224301948526465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29483999779264805196070573 11056499917224301948526465)
        ·
          refine ⟨8292374937918226461394849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11056499917224301948526465 8292374937918226461394849)
          ·
            refine ⟨6219281203438669846046137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8292374937918226461394849 6219281203438669846046137)
            ·
              refine ⟨4664460902579002384534603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6219281203438669846046137 4664460902579002384534603)
              ·
                refine ⟨6996691353868503576801905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4664460902579002384534603 6996691353868503576801905)
                ·
                  refine ⟨5247518515401377682601429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6996691353868503576801905 5247518515401377682601429)
                  ·
                    refine ⟨122988715204719789435971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5247518515401377682601429 122988715204719789435971)
                    ·
                      rfl

theorem cell23_718559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 7].length) (baseStart_718559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718559 prefixEnd_718559 := by exact prefixLift 718559
  have htrace : WordTrace (prefixWord ++ tailWord_718559) baseStart_718559 baseEnd_718559 := by
    simpa [prefixWord, tailWord_718559, baseEnd_718559] using wordTrace_append hprefix tailTrace_718559
  have hstable : (prefixWord ++ tailWord_718559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718559).length < 2 ^ (prefixWord ++ tailWord_718559).sum := by decide
  have hdescent : baseEnd_718559 < baseStart_718559 := by decide
  rcases family_descends (prefixWord ++ tailWord_718559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718589 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 3, 8]
def baseStart_718589 : Nat := 118140960795 + 718589 * 2 ^ 59
def prefixEnd_718589 : Nat := 4983230072969 + 3 ^ 40 * 718589 * 2
def baseEnd_718589 : Nat := 122993850011264750310925

theorem tailTrace_718589 : CollatzResearch.WordTrace tailWord_718589 prefixEnd_718589 122993850011264750310925 := by
  unfold tailWord_718589
  simp only [CollatzResearch.WordTrace]
  refine ⟨26209093993682253075654821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17472729329121502050436547 26209093993682253075654821)
  ·
    refine ⟨4914205123815422451685279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26209093993682253075654821 4914205123815422451685279)
    ·
      refine ⟨7371307685723133677527919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4914205123815422451685279 7371307685723133677527919)
      ·
        refine ⟨11056961528584700516291879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7371307685723133677527919 11056961528584700516291879)
        ·
          refine ⟨16585442292877050774437819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11056961528584700516291879 16585442292877050774437819)
          ·
            refine ⟨24878163439315576161656729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16585442292877050774437819 24878163439315576161656729)
            ·
              refine ⟨18658622579486682121242547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24878163439315576161656729 18658622579486682121242547)
              ·
                refine ⟨27987933869230023181863821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18658622579486682121242547 27987933869230023181863821)
                ·
                  refine ⟨10495475200961258693198933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27987933869230023181863821 10495475200961258693198933)
                  ·
                    refine ⟨122993850011264750310925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10495475200961258693198933 122993850011264750310925)
                    ·
                      rfl

theorem cell23_718589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_718589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718589 prefixEnd_718589 := by exact prefixLift 718589
  have htrace : WordTrace (prefixWord ++ tailWord_718589) baseStart_718589 baseEnd_718589 := by
    simpa [prefixWord, tailWord_718589, baseEnd_718589] using wordTrace_append hprefix tailTrace_718589
  have hstable : (prefixWord ++ tailWord_718589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718589).length < 2 ^ (prefixWord ++ tailWord_718589).sum := by decide
  have hdescent : baseEnd_718589 < baseStart_718589 := by decide
  rcases family_descends (prefixWord ++ tailWord_718589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718590 : List Nat := [4, 2, 2, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_718590 : Nat := 118140960795 + 718590 * 2 ^ 59
def prefixEnd_718590 : Nat := 4983230072969 + 3 ^ 40 * 718590 * 2
def baseEnd_718590 : Nat := 368982063514448747020271

theorem tailTrace_718590 : CollatzResearch.WordTrace tailWord_718590 prefixEnd_718590 368982063514448747020271 := by
  unfold tailWord_718590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3276141308334828780805153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17472753644452420164294149 3276141308334828780805153)
  ·
    refine ⟨2457105981251121585603865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3276141308334828780805153 2457105981251121585603865)
    ·
      refine ⟨1842829485938341189202899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2457105981251121585603865 1842829485938341189202899)
      ·
        refine ⟨2764244228907511783804349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1842829485938341189202899 2764244228907511783804349)
        ·
          refine ⟨1036591585840316918926631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2764244228907511783804349 1036591585840316918926631)
          ·
            refine ⟨1554887378760475378389947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036591585840316918926631 1554887378760475378389947)
            ·
              refine ⟨2332331068140713067584921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1554887378760475378389947 2332331068140713067584921)
              ·
                refine ⟨1749248301105534800688691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2332331068140713067584921 1749248301105534800688691)
                ·
                  refine ⟨2623872451658302201033037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1749248301105534800688691 2623872451658302201033037)
                  ·
                    refine ⟨983952169371863325387389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2623872451658302201033037 983952169371863325387389)
                    ·
                      refine ⟨368982063514448747020271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 983952169371863325387389 368982063514448747020271)
                      ·
                        rfl

theorem cell23_718590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_718590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718590 prefixEnd_718590 := by exact prefixLift 718590
  have htrace : WordTrace (prefixWord ++ tailWord_718590) baseStart_718590 baseEnd_718590 := by
    simpa [prefixWord, tailWord_718590, baseEnd_718590] using wordTrace_append hprefix tailTrace_718590
  have hstable : (prefixWord ++ tailWord_718590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718590).length < 2 ^ (prefixWord ++ tailWord_718590).sum := by decide
  have hdescent : baseEnd_718590 < baseStart_718590 := by decide
  rcases family_descends (prefixWord ++ tailWord_718590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718609 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 6]
def baseStart_718609 : Nat := 118140960795 + 718609 * 2 ^ 59
def prefixEnd_718609 : Nat := 4983230072969 + 3 ^ 40 * 718609 * 2
def baseEnd_718609 : Nat := 368991819646884172682683

theorem tailTrace_718609 : CollatzResearch.WordTrace tailWord_718609 prefixEnd_718609 368991819646884172682683 := by
  unfold tailWord_718609
  simp only [CollatzResearch.WordTrace]
  refine ⟨26209823453609796491382881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17473215635739864327588587 26209823453609796491382881)
  ·
    refine ⟨19657367590207347368537161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26209823453609796491382881 19657367590207347368537161)
    ·
      refine ⟨14743025692655510526402871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19657367590207347368537161 14743025692655510526402871)
      ·
        refine ⟨22114538538983265789604307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14743025692655510526402871 22114538538983265789604307)
        ·
          refine ⟨33171807808474898684406461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22114538538983265789604307 33171807808474898684406461)
          ·
            refine ⟨12439427928178087006652423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33171807808474898684406461 12439427928178087006652423)
            ·
              refine ⟨18659141892267130509978635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12439427928178087006652423 18659141892267130509978635)
              ·
                refine ⟨27988712838400695764967953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18659141892267130509978635 27988712838400695764967953)
                ·
                  refine ⟨20991534628800521823725965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27988712838400695764967953 20991534628800521823725965)
                  ·
                    refine ⟨7871825485800195683897237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20991534628800521823725965 7871825485800195683897237)
                    ·
                      refine ⟨368991819646884172682683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7871825485800195683897237 368991819646884172682683)
                      ·
                        rfl

theorem cell23_718609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_718609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718609 prefixEnd_718609 := by exact prefixLift 718609
  have htrace : WordTrace (prefixWord ++ tailWord_718609) baseStart_718609 baseEnd_718609 := by
    simpa [prefixWord, tailWord_718609, baseEnd_718609] using wordTrace_append hprefix tailTrace_718609
  have hstable : (prefixWord ++ tailWord_718609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718609).length < 2 ^ (prefixWord ++ tailWord_718609).sum := by decide
  have hdescent : baseEnd_718609 < baseStart_718609 := by decide
  rcases family_descends (prefixWord ++ tailWord_718609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718616 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 2, 4, 3]
def baseStart_718616 : Nat := 118140960795 + 718616 * 2 ^ 59
def prefixEnd_718616 : Nat := 4983230072969 + 3 ^ 40 * 718616 * 2
def baseEnd_718616 : Nat := 368995414011465645295151

theorem tailTrace_718616 : CollatzResearch.WordTrace tailWord_718616 prefixEnd_718616 368995414011465645295151 := by
  unfold tailWord_718616
  simp only [CollatzResearch.WordTrace]
  refine ⟨13105039382292218343443851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17473385843056291124591801 13105039382292218343443851)
  ·
    refine ⟨19657559073438327515165777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13105039382292218343443851 19657559073438327515165777)
    ·
      refine ⟨14743169305078745636374333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19657559073438327515165777 14743169305078745636374333)
      ·
        refine ⟨5528688489404529613640375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14743169305078745636374333 5528688489404529613640375)
        ·
          refine ⟨8293032734106794420460563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5528688489404529613640375 8293032734106794420460563)
          ·
            refine ⟨12439549101160191630690845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8293032734106794420460563 12439549101160191630690845)
            ·
              refine ⟨4664830912935071861509067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12439549101160191630690845 4664830912935071861509067)
              ·
                refine ⟨6997246369402607792263601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4664830912935071861509067 6997246369402607792263601)
                ·
                  refine ⟨5247934777051955844197701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6997246369402607792263601 5247934777051955844197701)
                  ·
                    refine ⟨983987770697241720787069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5247934777051955844197701 983987770697241720787069)
                    ·
                      refine ⟨368995414011465645295151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 983987770697241720787069 368995414011465645295151)
                      ·
                        rfl

theorem cell23_718616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_718616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718616 prefixEnd_718616 := by exact prefixLift 718616
  have htrace : WordTrace (prefixWord ++ tailWord_718616) baseStart_718616 baseEnd_718616 := by
    simpa [prefixWord, tailWord_718616, baseEnd_718616] using wordTrace_append hprefix tailTrace_718616
  have hstable : (prefixWord ++ tailWord_718616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718616).length < 2 ^ (prefixWord ++ tailWord_718616).sum := by decide
  have hdescent : baseEnd_718616 < baseStart_718616 := by decide
  rcases family_descends (prefixWord ++ tailWord_718616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718636 : List Nat := [2, 2, 1, 1, 1, 6, 1, 2, 7]
def baseStart_718636 : Nat := 118140960795 + 718636 * 2 ^ 59
def prefixEnd_718636 : Nat := 4983230072969 + 3 ^ 40 * 718636 * 2
def baseEnd_718636 : Nat := 41000631513839507449451

theorem tailTrace_718636 : CollatzResearch.WordTrace tailWord_718636 prefixEnd_718636 41000631513839507449451 := by
  unfold tailWord_718636
  simp only [CollatzResearch.WordTrace]
  refine ⟨13105404112255990051307881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17473872149674653401743841 13105404112255990051307881)
  ·
    refine ⟨9829053084191992538480911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13105404112255990051307881 9829053084191992538480911)
    ·
      refine ⟨14743579626287988807721367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9829053084191992538480911 14743579626287988807721367)
      ·
        refine ⟨22115369439431983211582051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14743579626287988807721367 22115369439431983211582051)
        ·
          refine ⟨33173054159147974817373077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22115369439431983211582051 33173054159147974817373077)
          ·
            refine ⟨1554986913710061319564363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33173054159147974817373077 1554986913710061319564363)
            ·
              refine ⟨2332480370565091979346545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1554986913710061319564363 2332480370565091979346545)
              ·
                refine ⟨1749360277923818984509909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2332480370565091979346545 1749360277923818984509909)
                ·
                  refine ⟨41000631513839507449451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1749360277923818984509909 41000631513839507449451)
                  ·
                    rfl

theorem cell23_718636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 7].length) (baseStart_718636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718636 prefixEnd_718636 := by exact prefixLift 718636
  have htrace : WordTrace (prefixWord ++ tailWord_718636) baseStart_718636 baseEnd_718636 := by
    simpa [prefixWord, tailWord_718636, baseEnd_718636] using wordTrace_append hprefix tailTrace_718636
  have hstable : (prefixWord ++ tailWord_718636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718636).length < 2 ^ (prefixWord ++ tailWord_718636).sum := by decide
  have hdescent : baseEnd_718636 < baseStart_718636 := by decide
  rcases family_descends (prefixWord ++ tailWord_718636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718639 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 8]
def baseStart_718639 : Nat := 118140960795 + 718639 * 2 ^ 59
def prefixEnd_718639 : Nat := 4983230072969 + 3 ^ 40 * 718639 * 2
def baseEnd_718639 : Nat := 369007224066519055307545

theorem tailTrace_718639 : CollatzResearch.WordTrace tailWord_718639 prefixEnd_718639 369007224066519055307545 := by
  unfold tailWord_718639
  simp only [CollatzResearch.WordTrace]
  refine ⟨26210917643501111614974971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17473945095667407743316647 26210917643501111614974971)
  ·
    refine ⟨39316376465251667422462457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26210917643501111614974971 39316376465251667422462457)
    ·
      refine ⟨29487282348938750566846843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39316376465251667422462457 29487282348938750566846843)
      ·
        refine ⟨44230923523408125850270265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29487282348938750566846843 44230923523408125850270265)
        ·
          refine ⟨33173192642556094387702699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44230923523408125850270265 33173192642556094387702699)
          ·
            refine ⟨49759788963834141581554049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33173192642556094387702699 49759788963834141581554049)
            ·
              refine ⟨37319841722875606186165537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49759788963834141581554049 37319841722875606186165537)
              ·
                refine ⟨27989881292156704639624153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37319841722875606186165537 27989881292156704639624153)
                ·
                  refine ⟨20992410969117528479718115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27989881292156704639624153 20992410969117528479718115)
                  ·
                    refine ⟨31488616453676292719577173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20992410969117528479718115 31488616453676292719577173)
                    ·
                      refine ⟨369007224066519055307545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 31488616453676292719577173 369007224066519055307545)
                      ·
                        rfl

theorem cell23_718639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_718639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718639 prefixEnd_718639 := by exact prefixLift 718639
  have htrace : WordTrace (prefixWord ++ tailWord_718639) baseStart_718639 baseEnd_718639 := by
    simpa [prefixWord, tailWord_718639, baseEnd_718639] using wordTrace_append hprefix tailTrace_718639
  have hstable : (prefixWord ++ tailWord_718639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718639).length < 2 ^ (prefixWord ++ tailWord_718639).sum := by decide
  have hdescent : baseEnd_718639 < baseStart_718639 := by decide
  rcases family_descends (prefixWord ++ tailWord_718639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718666 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 4, 5]
def baseStart_718666 : Nat := 118140960795 + 718666 * 2 ^ 59
def prefixEnd_718666 : Nat := 4983230072969 + 3 ^ 40 * 718666 * 2
def baseEnd_718666 : Nat := 123007029348063483223307

theorem tailTrace_718666 : CollatzResearch.WordTrace tailWord_718666 prefixEnd_718666 123007029348063483223307 := by
  unfold tailWord_718666
  simp only [CollatzResearch.WordTrace]
  refine ⟨6552975603600823806551963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17474601609602196817471901 6552975603600823806551963)
  ·
    refine ⟨9829463405401235709827945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6552975603600823806551963 9829463405401235709827945)
    ·
      refine ⟨7372097554050926782370959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9829463405401235709827945 7372097554050926782370959)
      ·
        refine ⟨11058146331076390173556439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7372097554050926782370959 11058146331076390173556439)
        ·
          refine ⟨16587219496614585260334659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11058146331076390173556439 16587219496614585260334659)
          ·
            refine ⟨24880829244921877890501989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16587219496614585260334659 24880829244921877890501989)
            ·
              refine ⟨4665155483422852104469123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24880829244921877890501989 4665155483422852104469123)
              ·
                refine ⟨6997733225134278156703685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4665155483422852104469123 6997733225134278156703685)
                ·
                  refine ⟨1312074979712677154381941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6997733225134278156703685 1312074979712677154381941)
                  ·
                    refine ⟨123007029348063483223307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1312074979712677154381941 123007029348063483223307)
                    ·
                      rfl

theorem cell23_718666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_718666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718666 prefixEnd_718666 := by exact prefixLift 718666
  have htrace : WordTrace (prefixWord ++ tailWord_718666) baseStart_718666 baseEnd_718666 := by
    simpa [prefixWord, tailWord_718666, baseEnd_718666] using wordTrace_append hprefix tailTrace_718666
  have hstable : (prefixWord ++ tailWord_718666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718666).length < 2 ^ (prefixWord ++ tailWord_718666).sum := by decide
  have hdescent : baseEnd_718666 < baseStart_718666 := by decide
  rcases family_descends (prefixWord ++ tailWord_718666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718696 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 2, 8]
def baseStart_718696 : Nat := 118140960795 + 718696 * 2 ^ 59
def prefixEnd_718696 : Nat := 4983230072969 + 3 ^ 40 * 718696 * 2
def baseEnd_718696 : Nat := 123012164154608444098261

theorem tailTrace_718696 : CollatzResearch.WordTrace tailWord_718696 prefixEnd_718696 123012164154608444098261 := by
  unfold tailWord_718696
  simp only [CollatzResearch.WordTrace]
  refine ⟨13106498302147305174899971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17475331069529740233199961 13106498302147305174899971)
  ·
    refine ⟨19659747453220957762349957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13106498302147305174899971 19659747453220957762349957)
    ·
      refine ⟨3686202647478929580440617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19659747453220957762349957 3686202647478929580440617)
      ·
        refine ⟨2764651985609197185330463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3686202647478929580440617 2764651985609197185330463)
        ·
          refine ⟨4146977978413795777995695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2764651985609197185330463 4146977978413795777995695)
          ·
            refine ⟨6220466967620693666993543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4146977978413795777995695 6220466967620693666993543)
            ·
              refine ⟨9330700451431040500490315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6220466967620693666993543 9330700451431040500490315)
              ·
                refine ⟨13996050677146560750735473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9330700451431040500490315 13996050677146560750735473)
                ·
                  refine ⟨10497038007859920563051605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13996050677146560750735473 10497038007859920563051605)
                  ·
                    refine ⟨123012164154608444098261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10497038007859920563051605 123012164154608444098261)
                    ·
                      rfl

theorem cell23_718696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_718696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718696 prefixEnd_718696 := by exact prefixLift 718696
  have htrace : WordTrace (prefixWord ++ tailWord_718696) baseStart_718696 baseEnd_718696 := by
    simpa [prefixWord, tailWord_718696, baseEnd_718696] using wordTrace_append hprefix tailTrace_718696
  have hstable : (prefixWord ++ tailWord_718696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718696).length < 2 ^ (prefixWord ++ tailWord_718696).sum := by decide
  have hdescent : baseEnd_718696 < baseStart_718696 := by decide
  rcases family_descends (prefixWord ++ tailWord_718696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718706 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_718706 : Nat := 118140960795 + 718706 * 2 ^ 59
def prefixEnd_718706 : Nat := 4983230072969 + 3 ^ 40 * 718706 * 2
def baseEnd_718706 : Nat := 369041627270370293169737

theorem tailTrace_718706 : CollatzResearch.WordTrace tailWord_718706 prefixEnd_718706 369041627270370293169737 := by
  unfold tailWord_718706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6553340333564595514415993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17475574222838921371775981 6553340333564595514415993)
  ·
    refine ⟨4915005250173446635811995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6553340333564595514415993 4915005250173446635811995)
    ·
      refine ⟨7372507875260169953717993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4915005250173446635811995 7372507875260169953717993)
      ·
        refine ⟨5529380906445127465288495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7372507875260169953717993 5529380906445127465288495)
        ·
          refine ⟨8294071359667691197932743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5529380906445127465288495 8294071359667691197932743)
          ·
            refine ⟨12441107039501536796899115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8294071359667691197932743 12441107039501536796899115)
            ·
              refine ⟨18661660559252305195348673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12441107039501536796899115 18661660559252305195348673)
              ·
                refine ⟨13996245419439228896511505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18661660559252305195348673 13996245419439228896511505)
                ·
                  refine ⟨10497184064579421672383629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13996245419439228896511505 10497184064579421672383629)
                  ·
                    refine ⟨3936444024217283127143861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10497184064579421672383629 3936444024217283127143861)
                    ·
                      refine ⟨369041627270370293169737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3936444024217283127143861 369041627270370293169737)
                      ·
                        rfl

theorem cell23_718706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_718706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718706 prefixEnd_718706 := by exact prefixLift 718706
  have htrace : WordTrace (prefixWord ++ tailWord_718706) baseStart_718706 baseEnd_718706 := by
    simpa [prefixWord, tailWord_718706, baseEnd_718706] using wordTrace_append hprefix tailTrace_718706
  have hstable : (prefixWord ++ tailWord_718706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718706).length < 2 ^ (prefixWord ++ tailWord_718706).sum := by decide
  have hdescent : baseEnd_718706 < baseStart_718706 := by decide
  rcases family_descends (prefixWord ++ tailWord_718706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718723 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 3]
def baseStart_718723 : Nat := 118140960795 + 718723 * 2 ^ 59
def prefixEnd_718723 : Nat := 4983230072969 + 3 ^ 40 * 718723 * 2
def baseEnd_718723 : Nat := 369050356441496726657159

theorem tailTrace_718723 : CollatzResearch.WordTrace tailWord_718723 prefixEnd_718723 369050356441496726657159 := by
  unfold tailWord_718723
  simp only [CollatzResearch.WordTrace]
  refine ⟨26213981375196793961032823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17475987583464529307355215 26213981375196793961032823)
  ·
    refine ⟨39320972062795190941549235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26213981375196793961032823 39320972062795190941549235)
    ·
      refine ⟨58981458094192786412323853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39320972062795190941549235 58981458094192786412323853)
      ·
        refine ⟨22118046785322294904621445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58981458094192786412323853 22118046785322294904621445)
        ·
          refine ⟨4147133772247930294616521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22118046785322294904621445 4147133772247930294616521)
          ·
            refine ⟨3110350329185947720962391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4147133772247930294616521 3110350329185947720962391)
            ·
              refine ⟨4665525493778921581443587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3110350329185947720962391 4665525493778921581443587)
              ·
                refine ⟨6998288240668382372165381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4665525493778921581443587 6998288240668382372165381)
                ·
                  refine ⟨1312179045125321694781009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6998288240668382372165381 1312179045125321694781009)
                  ·
                    refine ⟨984134283843991271085757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1312179045125321694781009 984134283843991271085757)
                    ·
                      refine ⟨369050356441496726657159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 984134283843991271085757 369050356441496726657159)
                      ·
                        rfl

theorem cell23_718723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_718723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718723 prefixEnd_718723 := by exact prefixLift 718723
  have htrace : WordTrace (prefixWord ++ tailWord_718723) baseStart_718723 baseEnd_718723 := by
    simpa [prefixWord, tailWord_718723, baseEnd_718723] using wordTrace_append hprefix tailTrace_718723
  have hstable : (prefixWord ++ tailWord_718723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718723).length < 2 ^ (prefixWord ++ tailWord_718723).sum := by decide
  have hdescent : baseEnd_718723 < baseStart_718723 := by decide
  rcases family_descends (prefixWord ++ tailWord_718723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718743 : List Nat := [1, 1, 3, 3, 1, 4, 1, 3, 6]
def baseStart_718743 : Nat := 118140960795 + 718743 * 2 ^ 59
def prefixEnd_718743 : Nat := 4983230072969 + 3 ^ 40 * 718743 * 2
def baseEnd_718743 : Nat := 41006736228287405378563

theorem tailTrace_718743 : CollatzResearch.WordTrace tailWord_718743 prefixEnd_718743 41006736228287405378563 := by
  unfold tailWord_718743
  simp only [CollatzResearch.WordTrace]
  refine ⟨26214710835124337376760883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17476473890082891584507255 26214710835124337376760883)
  ·
    refine ⟨39322066252686506065141325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26214710835124337376760883 39322066252686506065141325)
    ·
      refine ⟨14745774844757439774427997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39322066252686506065141325 14745774844757439774427997)
      ·
        refine ⟨5529665566784039915410499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14745774844757439774427997 5529665566784039915410499)
        ·
          refine ⟨8294498350176059873115749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5529665566784039915410499 8294498350176059873115749)
          ·
            refine ⟨1555218440658011226209203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8294498350176059873115749 1555218440658011226209203)
            ·
              refine ⟨2332827660987016839313805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1555218440658011226209203 2332827660987016839313805)
              ·
                refine ⟨874810372870131314742677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2332827660987016839313805 874810372870131314742677)
                ·
                  refine ⟨41006736228287405378563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 874810372870131314742677 41006736228287405378563)
                  ·
                    rfl

theorem cell23_718743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 6].length) (baseStart_718743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718743 prefixEnd_718743 := by exact prefixLift 718743
  have htrace : WordTrace (prefixWord ++ tailWord_718743) baseStart_718743 baseEnd_718743 := by
    simpa [prefixWord, tailWord_718743, baseEnd_718743] using wordTrace_append hprefix tailTrace_718743
  have hstable : (prefixWord ++ tailWord_718743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718743).length < 2 ^ (prefixWord ++ tailWord_718743).sum := by decide
  have hdescent : baseEnd_718743 < baseStart_718743 := by decide
  rcases family_descends (prefixWord ++ tailWord_718743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718816 : List Nat := [2, 1, 1, 3, 1, 1, 1, 13]
def baseStart_718816 : Nat := 118140960795 + 718816 * 2 ^ 59
def prefixEnd_718816 : Nat := 4983230072969 + 3 ^ 40 * 718816 * 2
def baseEnd_718816 : Nat := 13670300375643143066453

theorem tailTrace_718816 : CollatzResearch.WordTrace tailWord_718816 prefixEnd_718816 13670300375643143066453 := by
  unfold tailWord_718816
  simp only [CollatzResearch.WordTrace]
  refine ⟨13108686681929935422084151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17478248909239913896112201 13108686681929935422084151)
  ·
    refine ⟨19663030022894903133126227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13108686681929935422084151 19663030022894903133126227)
    ·
      refine ⟨29494545034342354699689341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19663030022894903133126227 29494545034342354699689341)
      ·
        refine ⟨11060454387878383012383503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29494545034342354699689341 11060454387878383012383503)
        ·
          refine ⟨16590681581817574518575255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11060454387878383012383503 16590681581817574518575255)
          ·
            refine ⟨24886022372726361777862883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16590681581817574518575255 24886022372726361777862883)
            ·
              refine ⟨37329033559089542666794325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24886022372726361777862883 37329033559089542666794325)
              ·
                refine ⟨13670300375643143066453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 37329033559089542666794325 13670300375643143066453)
                ·
                  rfl

theorem cell23_718816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 13].length) (baseStart_718816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718816 prefixEnd_718816 := by exact prefixLift 718816
  have htrace : WordTrace (prefixWord ++ tailWord_718816) baseStart_718816 baseEnd_718816 := by
    simpa [prefixWord, tailWord_718816, baseEnd_718816] using wordTrace_append hprefix tailTrace_718816
  have hstable : (prefixWord ++ tailWord_718816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718816).length < 2 ^ (prefixWord ++ tailWord_718816).sum := by decide
  have hdescent : baseEnd_718816 < baseStart_718816 := by decide
  rcases family_descends (prefixWord ++ tailWord_718816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718833 : List Nat := [1, 2, 2, 2, 5, 1, 10]
def baseStart_718833 : Nat := 118140960795 + 718833 * 2 ^ 59
def prefixEnd_718833 : Nat := 4983230072969 + 3 ^ 40 * 718833 * 2
def baseEnd_718833 : Nat := 4556874559425818472613

theorem tailTrace_718833 : CollatzResearch.WordTrace tailWord_718833 prefixEnd_718833 4556874559425818472613 := by
  unfold tailWord_718833
  simp only [CollatzResearch.WordTrace]
  refine ⟨26217993404798282747537153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17478662269865521831691435 26217993404798282747537153)
  ·
    refine ⟨19663495053598712060652865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26217993404798282747537153 19663495053598712060652865)
    ·
      refine ⟨14747621290199034045489649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19663495053598712060652865 14747621290199034045489649)
      ·
        refine ⟨11060715967649275534117237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14747621290199034045489649 11060715967649275534117237)
        ·
          refine ⟨1036942121967119581323491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11060715967649275534117237 1036942121967119581323491)
          ·
            refine ⟨1555413182950679371985237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036942121967119581323491 1555413182950679371985237)
            ·
              refine ⟨4556874559425818472613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1555413182950679371985237 4556874559425818472613)
              ·
                rfl

theorem cell23_718833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 10].length) (baseStart_718833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718833 prefixEnd_718833 := by exact prefixLift 718833
  have htrace : WordTrace (prefixWord ++ tailWord_718833) baseStart_718833 baseEnd_718833 := by
    simpa [prefixWord, tailWord_718833, baseEnd_718833] using wordTrace_append hprefix tailTrace_718833
  have hstable : (prefixWord ++ tailWord_718833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718833).length < 2 ^ (prefixWord ++ tailWord_718833).sum := by decide
  have hdescent : baseEnd_718833 < baseStart_718833 := by decide
  rcases family_descends (prefixWord ++ tailWord_718833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718843 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 3]
def baseStart_718843 : Nat := 118140960795 + 718843 * 2 ^ 59
def prefixEnd_718843 : Nat := 4983230072969 + 3 ^ 40 * 718843 * 2
def baseEnd_718843 : Nat := 369111974120036257156607

theorem tailTrace_718843 : CollatzResearch.WordTrace tailWord_718843 prefixEnd_718843 369111974120036257156607 := by
  unfold tailWord_718843
  simp only [CollatzResearch.WordTrace]
  refine ⟨26218358134762054455401183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17478905423174702970267455 26218358134762054455401183)
  ·
    refine ⟨39327537202143081683101775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26218358134762054455401183 39327537202143081683101775)
    ·
      refine ⟨58991305803214622524652663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39327537202143081683101775 58991305803214622524652663)
      ·
        refine ⟨88486958704821933786978995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58991305803214622524652663 88486958704821933786978995)
        ·
          refine ⟨132730438057232900680468493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88486958704821933786978995 132730438057232900680468493)
          ·
            refine ⟨49773914271462337755175685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132730438057232900680468493 49773914271462337755175685)
            ·
              refine ⟨9332608925899188329095441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49773914271462337755175685 9332608925899188329095441)
              ·
                refine ⟨6999456694424391246821581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9332608925899188329095441 6999456694424391246821581)
                ·
                  refine ⟨2624796260409146717558093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6999456694424391246821581 2624796260409146717558093)
                  ·
                    refine ⟨984298597653430019084285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2624796260409146717558093 984298597653430019084285)
                    ·
                      refine ⟨369111974120036257156607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 984298597653430019084285 369111974120036257156607)
                      ·
                        rfl

theorem cell23_718843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 3].length) (baseStart_718843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718843 prefixEnd_718843 := by exact prefixLift 718843
  have htrace : WordTrace (prefixWord ++ tailWord_718843) baseStart_718843 baseEnd_718843 := by
    simpa [prefixWord, tailWord_718843, baseEnd_718843] using wordTrace_append hprefix tailTrace_718843
  have hstable : (prefixWord ++ tailWord_718843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718843).length < 2 ^ (prefixWord ++ tailWord_718843).sum := by decide
  have hdescent : baseEnd_718843 < baseStart_718843 := by decide
  rcases family_descends (prefixWord ++ tailWord_718843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718844 : List Nat := [2, 2, 2, 1, 2, 2, 1, 6, 1, 2, 2]
def baseStart_718844 : Nat := 118140960795 + 718844 * 2 ^ 59
def prefixEnd_718844 : Nat := 4983230072969 + 3 ^ 40 * 718844 * 2
def baseEnd_718844 : Nat := 369112487600690753244103

theorem tailTrace_718844 : CollatzResearch.WordTrace tailWord_718844 prefixEnd_718844 369112487600690753244103 := by
  unfold tailWord_718844
  simp only [CollatzResearch.WordTrace]
  refine ⟨13109197303879215813093793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17478929738505621084125057 13109197303879215813093793)
  ·
    refine ⟨9831897977909411859820345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13109197303879215813093793 9831897977909411859820345)
    ·
      refine ⟨7373923483432058894865259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9831897977909411859820345 7373923483432058894865259)
      ·
        refine ⟨11060885225148088342297889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7373923483432058894865259 11060885225148088342297889)
        ·
          refine ⟨8295663918861066256723417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11060885225148088342297889 8295663918861066256723417)
          ·
            refine ⟨6221747939145799692542563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8295663918861066256723417 6221747939145799692542563)
            ·
              refine ⟨9332621908718699538813845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6221747939145799692542563 9332621908718699538813845)
              ·
                refine ⟨437466651971189040881899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9332621908718699538813845 437466651971189040881899)
                ·
                  refine ⟨656199977956783561322849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 437466651971189040881899 656199977956783561322849)
                  ·
                    refine ⟨492149983467587670992137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 656199977956783561322849 492149983467587670992137)
                    ·
                      refine ⟨369112487600690753244103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 492149983467587670992137 369112487600690753244103)
                      ·
                        rfl

theorem cell23_718844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 1, 2, 2].length) (baseStart_718844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718844 prefixEnd_718844 := by exact prefixLift 718844
  have htrace : WordTrace (prefixWord ++ tailWord_718844) baseStart_718844 baseEnd_718844 := by
    simpa [prefixWord, tailWord_718844, baseEnd_718844] using wordTrace_append hprefix tailTrace_718844
  have hstable : (prefixWord ++ tailWord_718844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718844).length < 2 ^ (prefixWord ++ tailWord_718844).sum := by decide
  have hdescent : baseEnd_718844 < baseStart_718844 := by decide
  rcases family_descends (prefixWord ++ tailWord_718844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718877 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_718877 : Nat := 118140960795 + 718877 * 2 ^ 59
def prefixEnd_718877 : Nat := 4983230072969 + 3 ^ 40 * 718877 * 2
def baseEnd_718877 : Nat := 369129432462289124131451

theorem tailTrace_718877 : CollatzResearch.WordTrace tailWord_718877 prefixEnd_718877 369129432462289124131451 := by
  unfold tailWord_718877
  simp only [CollatzResearch.WordTrace]
  refine ⟨26219598216638878262138885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17479732144425918841425923 26219598216638878262138885)
  ·
    refine ⟨4916174665619789674151041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26219598216638878262138885 4916174665619789674151041)
    ·
      refine ⟨3687130999214842255613281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4916174665619789674151041 3687130999214842255613281)
      ·
        refine ⟨2765348249411131691709961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3687130999214842255613281 2765348249411131691709961)
        ·
          refine ⟨2074011187058348768782471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2765348249411131691709961 2074011187058348768782471)
          ·
            refine ⟨3111016780587523153173707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2074011187058348768782471 3111016780587523153173707)
            ·
              refine ⟨4666525170881284729760561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3111016780587523153173707 4666525170881284729760561)
              ·
                refine ⟨3499893878160963547320421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4666525170881284729760561 3499893878160963547320421)
                ·
                  refine ⟨656230102155180665122579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3499893878160963547320421 656230102155180665122579)
                  ·
                    refine ⟨984345153232770997683869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 656230102155180665122579 984345153232770997683869)
                    ·
                      refine ⟨369129432462289124131451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 984345153232770997683869 369129432462289124131451)
                      ·
                        rfl

theorem cell23_718877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_718877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718877 prefixEnd_718877 := by exact prefixLift 718877
  have htrace : WordTrace (prefixWord ++ tailWord_718877) baseStart_718877 baseEnd_718877 := by
    simpa [prefixWord, tailWord_718877, baseEnd_718877] using wordTrace_append hprefix tailTrace_718877
  have hstable : (prefixWord ++ tailWord_718877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718877).length < 2 ^ (prefixWord ++ tailWord_718877).sum := by decide
  have hdescent : baseEnd_718877 < baseStart_718877 := by decide
  rcases family_descends (prefixWord ++ tailWord_718877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718957 : List Nat := [1, 5, 1, 1, 2, 1, 3, 4, 5]
def baseStart_718957 : Nat := 118140960795 + 718957 * 2 ^ 59
def prefixEnd_718957 : Nat := 4983230072969 + 3 ^ 40 * 718957 * 2
def baseEnd_718957 : Nat := 41018945657183201236787

theorem tailTrace_718957 : CollatzResearch.WordTrace tailWord_718957 prefixEnd_718957 41018945657183201236787 := by
  unfold tailWord_718957
  simp only [CollatzResearch.WordTrace]
  refine ⟨26222516056349051925051125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17481677370899367950034083 26222516056349051925051125)
  ·
    refine ⟨2458360880282723617973543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26222516056349051925051125 2458360880282723617973543)
    ·
      refine ⟨3687541320424085426960315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2458360880282723617973543 3687541320424085426960315)
      ·
        refine ⟨5531311980636128140440473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3687541320424085426960315 5531311980636128140440473)
        ·
          refine ⟨4148483985477096105330355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5531311980636128140440473 4148483985477096105330355)
          ·
            refine ⟨6222725978215644157995533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4148483985477096105330355 6222725978215644157995533)
            ·
              refine ⟨2333522241830866559248325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6222725978215644157995533 2333522241830866559248325)
              ·
                refine ⟨437535420343287479859061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2333522241830866559248325 437535420343287479859061)
                ·
                  refine ⟨41018945657183201236787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 437535420343287479859061 41018945657183201236787)
                  ·
                    rfl

theorem cell23_718957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_718957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_718957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_718957 prefixEnd_718957 := by exact prefixLift 718957
  have htrace : WordTrace (prefixWord ++ tailWord_718957) baseStart_718957 baseEnd_718957 := by
    simpa [prefixWord, tailWord_718957, baseEnd_718957] using wordTrace_append hprefix tailTrace_718957
  have hstable : (prefixWord ++ tailWord_718957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718957).length < 2 ^ (prefixWord ++ tailWord_718957).sum := by decide
  have hdescent : baseEnd_718957 < baseStart_718957 := by decide
  rcases family_descends (prefixWord ++ tailWord_718957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719003 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 6]
def baseStart_719003 : Nat := 118140960795 + 719003 * 2 ^ 59
def prefixEnd_719003 : Nat := 4983230072969 + 3 ^ 40 * 719003 * 2
def baseEnd_719003 : Nat := 369194131024755631155871

theorem tailTrace_719003 : CollatzResearch.WordTrace tailWord_719003 prefixEnd_719003 369194131024755631155871 := by
  unfold tailWord_719003
  simp only [CollatzResearch.WordTrace]
  refine ⟨26224193814182401781225663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17482795876121601187483775 26224193814182401781225663)
  ·
    refine ⟨39336290721273602671838495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26224193814182401781225663 39336290721273602671838495)
    ·
      refine ⟨59004436081910404007757743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39336290721273602671838495 59004436081910404007757743)
      ·
        refine ⟨88506654122865606011636615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59004436081910404007757743 88506654122865606011636615)
        ·
          refine ⟨132759981184298409017454923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88506654122865606011636615 132759981184298409017454923)
          ·
            refine ⟨199139971776447613526182385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132759981184298409017454923 199139971776447613526182385)
            ·
              refine ⟨149354978832335710144636789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199139971776447613526182385 149354978832335710144636789)
              ·
                refine ⟨14002029265531472826059699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149354978832335710144636789 14002029265531472826059699)
                ·
                  refine ⟨21003043898297209239089549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14002029265531472826059699 21003043898297209239089549)
                  ·
                    refine ⟨7876141461861453464658581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21003043898297209239089549 7876141461861453464658581)
                    ·
                      refine ⟨369194131024755631155871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7876141461861453464658581 369194131024755631155871)
                      ·
                        rfl

theorem cell23_719003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 6].length) (baseStart_719003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719003 prefixEnd_719003 := by exact prefixLift 719003
  have htrace : WordTrace (prefixWord ++ tailWord_719003) baseStart_719003 baseEnd_719003 := by
    simpa [prefixWord, tailWord_719003, baseEnd_719003] using wordTrace_append hprefix tailTrace_719003
  have hstable : (prefixWord ++ tailWord_719003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719003).length < 2 ^ (prefixWord ++ tailWord_719003).sum := by decide
  have hdescent : baseEnd_719003 < baseStart_719003 := by decide
  rcases family_descends (prefixWord ++ tailWord_719003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719057 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 5, 1, 3]
def baseStart_719057 : Nat := 118140960795 + 719057 * 2 ^ 59
def prefixEnd_719057 : Nat := 4983230072969 + 3 ^ 40 * 719057 * 2
def baseEnd_719057 : Nat := 369221858980098419880623

theorem tailTrace_719057 : CollatzResearch.WordTrace tailWord_719057 prefixEnd_719057 369221858980098419880623 := by
  unfold tailWord_719057
  simp only [CollatzResearch.WordTrace]
  refine ⟨26226163355986769003691425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17484108903991179335794283 26226163355986769003691425)
  ·
    refine ⟨19669622516990076752768569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26226163355986769003691425 19669622516990076752768569)
    ·
      refine ⟨14752216887742557564576427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19669622516990076752768569 14752216887742557564576427)
      ·
        refine ⟨22128325331613836346864641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14752216887742557564576427 22128325331613836346864641)
        ·
          refine ⟨16596243998710377260148481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22128325331613836346864641 16596243998710377260148481)
          ·
            refine ⟨12447182999032782945111361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16596243998710377260148481 12447182999032782945111361)
            ·
              refine ⟨9335387249274587208833521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12447182999032782945111361 9335387249274587208833521)
              ·
                refine ⟨7001540436955940406625141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9335387249274587208833521 7001540436955940406625141)
                ·
                  refine ⟨656394415964619413121107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7001540436955940406625141 656394415964619413121107)
                  ·
                    refine ⟨984591623946929119681661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 656394415964619413121107 984591623946929119681661)
                    ·
                      refine ⟨369221858980098419880623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 984591623946929119681661 369221858980098419880623)
                      ·
                        rfl

theorem cell23_719057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 1, 3].length) (baseStart_719057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719057 prefixEnd_719057 := by exact prefixLift 719057
  have htrace : WordTrace (prefixWord ++ tailWord_719057) baseStart_719057 baseEnd_719057 := by
    simpa [prefixWord, tailWord_719057, baseEnd_719057] using wordTrace_append hprefix tailTrace_719057
  have hstable : (prefixWord ++ tailWord_719057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719057).length < 2 ^ (prefixWord ++ tailWord_719057).sum := by decide
  have hdescent : baseEnd_719057 < baseStart_719057 := by decide
  rcases family_descends (prefixWord ++ tailWord_719057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719067 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 4, 3, 2]
def baseStart_719067 : Nat := 118140960795 + 719067 * 2 ^ 59
def prefixEnd_719067 : Nat := 4983230072969 + 3 ^ 40 * 719067 * 2
def baseEnd_719067 : Nat := 369226993786643380755577

theorem tailTrace_719067 : CollatzResearch.WordTrace tailWord_719067 prefixEnd_719067 369226993786643380755577 := by
  unfold tailWord_719067
  simp only [CollatzResearch.WordTrace]
  refine ⟨26226528085950540711555455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17484352057300360474370303 26226528085950540711555455)
  ·
    refine ⟨39339792128925811067333183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26226528085950540711555455 39339792128925811067333183)
    ·
      refine ⟨59009688193388716600999775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39339792128925811067333183 59009688193388716600999775)
      ·
        refine ⟨88514532290083074901499663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59009688193388716600999775 88514532290083074901499663)
        ·
          refine ⟨132771798435124612352249495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88514532290083074901499663 132771798435124612352249495)
          ·
            refine ⟨199157697652686918528374243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132771798435124612352249495 199157697652686918528374243)
            ·
              refine ⟨298736546479030377792561365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199157697652686918528374243 298736546479030377792561365)
              ·
                refine ⟨7001637808102274479513157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 298736546479030377792561365 7001637808102274479513157)
                ·
                  refine ⟨1312807089019176464908717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7001637808102274479513157 1312807089019176464908717)
                  ·
                    refine ⟨492302658382191174340769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1312807089019176464908717 492302658382191174340769)
                    ·
                      refine ⟨369226993786643380755577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 492302658382191174340769 369226993786643380755577)
                      ·
                        rfl

theorem cell23_719067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 3, 2].length) (baseStart_719067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719067 prefixEnd_719067 := by exact prefixLift 719067
  have htrace : WordTrace (prefixWord ++ tailWord_719067) baseStart_719067 baseEnd_719067 := by
    simpa [prefixWord, tailWord_719067, baseEnd_719067] using wordTrace_append hprefix tailTrace_719067
  have hstable : (prefixWord ++ tailWord_719067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719067).length < 2 ^ (prefixWord ++ tailWord_719067).sum := by decide
  have hdescent : baseEnd_719067 < baseStart_719067 := by decide
  rcases family_descends (prefixWord ++ tailWord_719067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719068 : List Nat := [2, 2, 5, 2, 1, 2, 1, 1, 3, 4]
def baseStart_719068 : Nat := 118140960795 + 719068 * 2 ^ 59
def prefixEnd_719068 : Nat := 4983230072969 + 3 ^ 40 * 719068 * 2
def baseEnd_719068 : Nat := 123075835755765958947691

theorem tailTrace_719068 : CollatzResearch.WordTrace tailWord_719068 prefixEnd_719068 123075835755765958947691 := by
  unfold tailWord_719068
  simp only [CollatzResearch.WordTrace]
  refine ⟨13113282279473458941170929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17484376372631278588227905 13113282279473458941170929)
  ·
    refine ⟨9834961709605094205878197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13113282279473458941170929 9834961709605094205878197)
    ·
      refine ⟨922027660275477581801081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9834961709605094205878197 922027660275477581801081)
      ·
        refine ⟨691520745206608186350811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 922027660275477581801081 691520745206608186350811)
        ·
          refine ⟨1037281117809912279526217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691520745206608186350811 1037281117809912279526217)
          ·
            refine ⟨777960838357434209644663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1037281117809912279526217 777960838357434209644663)
            ·
              refine ⟨1166941257536151314466995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777960838357434209644663 1166941257536151314466995)
              ·
                refine ⟨1750411886304226971700493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1166941257536151314466995 1750411886304226971700493)
                ·
                  refine ⟨656404457364085114387685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1750411886304226971700493 656404457364085114387685)
                  ·
                    refine ⟨123075835755765958947691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 656404457364085114387685 123075835755765958947691)
                    ·
                      rfl

theorem cell23_719068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_719068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719068 prefixEnd_719068 := by exact prefixLift 719068
  have htrace : WordTrace (prefixWord ++ tailWord_719068) baseStart_719068 baseEnd_719068 := by
    simpa [prefixWord, tailWord_719068, baseEnd_719068] using wordTrace_append hprefix tailTrace_719068
  have hstable : (prefixWord ++ tailWord_719068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719068).length < 2 ^ (prefixWord ++ tailWord_719068).sum := by decide
  have hdescent : baseEnd_719068 < baseStart_719068 := by decide
  rcases family_descends (prefixWord ++ tailWord_719068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719094 : List Nat := [5, 1, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_719094 : Nat := 118140960795 + 719094 * 2 ^ 59
def prefixEnd_719094 : Nat := 4983230072969 + 3 ^ 40 * 719094 * 2
def baseEnd_719094 : Nat := 123080285921438258372651

theorem tailTrace_719094 : CollatzResearch.WordTrace tailWord_719094 prefixEnd_719094 123080285921438258372651 := by
  unfold tailWord_719094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1639219553553295270174271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17485008571235149548525557 1639219553553295270174271)
  ·
    refine ⟨2458829330329942905261407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1639219553553295270174271 2458829330329942905261407)
    ·
      refine ⟨3688243995494914357892111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2458829330329942905261407 3688243995494914357892111)
      ·
        refine ⟨5532365993242371536838167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3688243995494914357892111 5532365993242371536838167)
        ·
          refine ⟨8298548989863557305257251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5532365993242371536838167 8298548989863557305257251)
          ·
            refine ⟨12447823484795335957885877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8298548989863557305257251 12447823484795335957885877)
            ·
              refine ⟨1166983451699562746051801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12447823484795335957885877 1166983451699562746051801)
              ·
                refine ⟨875237588774672059538851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1166983451699562746051801 875237588774672059538851)
                ·
                  refine ⟨1312856383162008089308277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875237588774672059538851 1312856383162008089308277)
                  ·
                    refine ⟨123080285921438258372651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1312856383162008089308277 123080285921438258372651)
                    ·
                      rfl

theorem cell23_719094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_719094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719094 prefixEnd_719094 := by exact prefixLift 719094
  have htrace : WordTrace (prefixWord ++ tailWord_719094) baseStart_719094 baseEnd_719094 := by
    simpa [prefixWord, tailWord_719094, baseEnd_719094] using wordTrace_append hprefix tailTrace_719094
  have hstable : (prefixWord ++ tailWord_719094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719094).length < 2 ^ (prefixWord ++ tailWord_719094).sum := by decide
  have hdescent : baseEnd_719094 < baseStart_719094 := by decide
  rcases family_descends (prefixWord ++ tailWord_719094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719097 : List Nat := [1, 2, 1, 3, 1, 1, 2, 6, 1, 1, 4]
def baseStart_719097 : Nat := 118140960795 + 719097 * 2 ^ 59
def prefixEnd_719097 : Nat := 4983230072969 + 3 ^ 40 * 719097 * 2
def baseEnd_719097 : Nat := 369242398206278263380439

theorem tailTrace_719097 : CollatzResearch.WordTrace tailWord_719097 prefixEnd_719097 369242398206278263380439 := by
  unfold tailWord_719097
  simp only [CollatzResearch.WordTrace]
  refine ⟨26227622275841855835147545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17485081517227903890098363 26227622275841855835147545)
  ·
    refine ⟨19670716706881391876360659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26227622275841855835147545 19670716706881391876360659)
    ·
      refine ⟨29506075060322087814540989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19670716706881391876360659 29506075060322087814540989)
      ·
        refine ⟨11064778147620782930452871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29506075060322087814540989 11064778147620782930452871)
        ·
          refine ⟨16597167221431174395679307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11064778147620782930452871 16597167221431174395679307)
          ·
            refine ⟨24895750832146761593518961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16597167221431174395679307 24895750832146761593518961)
            ·
              refine ⟨18671813124110071195139221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24895750832146761593518961 18671813124110071195139221)
              ·
                refine ⟨875241240192659587272151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18671813124110071195139221 875241240192659587272151)
                ·
                  refine ⟨1312861860288989380908227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875241240192659587272151 1312861860288989380908227)
                  ·
                    refine ⟨1969292790433484071362341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1312861860288989380908227 1969292790433484071362341)
                    ·
                      refine ⟨369242398206278263380439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1969292790433484071362341 369242398206278263380439)
                      ·
                        rfl

theorem cell23_719097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_719097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719097 prefixEnd_719097 := by exact prefixLift 719097
  have htrace : WordTrace (prefixWord ++ tailWord_719097) baseStart_719097 baseEnd_719097 := by
    simpa [prefixWord, tailWord_719097, baseEnd_719097] using wordTrace_append hprefix tailTrace_719097
  have hstable : (prefixWord ++ tailWord_719097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719097).length < 2 ^ (prefixWord ++ tailWord_719097).sum := by decide
  have hdescent : baseEnd_719097 < baseStart_719097 := by decide
  rcases family_descends (prefixWord ++ tailWord_719097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719154 : List Nat := [3, 2, 1, 1, 5, 1, 3, 7]
def baseStart_719154 : Nat := 118140960795 + 719154 * 2 ^ 59
def prefixEnd_719154 : Nat := 4983230072969 + 3 ^ 40 * 719154 * 2
def baseEnd_719154 : Nat := 13676728392725353346951

theorem tailTrace_719154 : CollatzResearch.WordTrace tailWord_719154 prefixEnd_719154 13676728392725353346951 := by
  unfold tailWord_719154
  simp only [CollatzResearch.WordTrace]
  refine ⟨6557425309158838642493129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17486467491090236379981677 6557425309158838642493129)
  ·
    refine ⟨4918068981869128981869847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6557425309158838642493129 4918068981869128981869847)
    ·
      refine ⟨7377103472803693472804771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4918068981869128981869847 7377103472803693472804771)
      ·
        refine ⟨11065655209205540209207157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7377103472803693472804771 11065655209205540209207157)
        ·
          refine ⟨1037405175863019394613171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11065655209205540209207157 1037405175863019394613171)
          ·
            refine ⟨1556107763794529091919757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037405175863019394613171 1556107763794529091919757)
            ·
              refine ⟨583540411422948409469909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1556107763794529091919757 583540411422948409469909)
              ·
                refine ⟨13676728392725353346951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 583540411422948409469909 13676728392725353346951)
                ·
                  rfl

theorem cell23_719154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 7].length) (baseStart_719154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719154 prefixEnd_719154 := by exact prefixLift 719154
  have htrace : WordTrace (prefixWord ++ tailWord_719154) baseStart_719154 baseEnd_719154 := by
    simpa [prefixWord, tailWord_719154, baseEnd_719154] using wordTrace_append hprefix tailTrace_719154
  have hstable : (prefixWord ++ tailWord_719154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719154).length < 2 ^ (prefixWord ++ tailWord_719154).sum := by decide
  have hdescent : baseEnd_719154 < baseStart_719154 := by decide
  rcases family_descends (prefixWord ++ tailWord_719154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719164 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 4, 1, 3]
def baseStart_719164 : Nat := 118140960795 + 719164 * 2 ^ 59
def prefixEnd_719164 : Nat := 4983230072969 + 3 ^ 40 * 719164 * 2
def baseEnd_719164 : Nat := 369276801410129501242631

theorem tailTrace_719164 : CollatzResearch.WordTrace tailWord_719164 prefixEnd_719164 369276801410129501242631 := by
  unfold tailWord_719164
  simp only [CollatzResearch.WordTrace]
  refine ⟨13115032983299563138918273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17486710644399417518557697 13115032983299563138918273)
  ·
    refine ⟨9836274737474672354188705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13115032983299563138918273 9836274737474672354188705)
    ·
      refine ⟨7377206053106004265641529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9836274737474672354188705 7377206053106004265641529)
      ·
        refine ⟨5532904539829503199231147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7377206053106004265641529 5532904539829503199231147)
        ·
          refine ⟨8299356809744254798846721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5532904539829503199231147 8299356809744254798846721)
          ·
            refine ⟨6224517607308191099135041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8299356809744254798846721 6224517607308191099135041)
            ·
              refine ⟨4668388205481143324351281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6224517607308191099135041 4668388205481143324351281)
              ·
                refine ⟨3501291154110857493263461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4668388205481143324351281 3501291154110857493263461)
                ·
                  refine ⟨656492091395785779986899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3501291154110857493263461 656492091395785779986899)
                  ·
                    refine ⟨984738137093678669980349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 656492091395785779986899 984738137093678669980349)
                    ·
                      refine ⟨369276801410129501242631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 984738137093678669980349 369276801410129501242631)
                      ·
                        rfl

theorem cell23_719164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_719164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719164 prefixEnd_719164 := by exact prefixLift 719164
  have htrace : WordTrace (prefixWord ++ tailWord_719164) baseStart_719164 baseEnd_719164 := by
    simpa [prefixWord, tailWord_719164, baseEnd_719164] using wordTrace_append hprefix tailTrace_719164
  have hstable : (prefixWord ++ tailWord_719164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719164).length < 2 ^ (prefixWord ++ tailWord_719164).sum := by decide
  have hdescent : baseEnd_719164 < baseStart_719164 := by decide
  rcases family_descends (prefixWord ++ tailWord_719164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719208 : List Nat := [2, 1, 4, 2, 2, 2, 2, 2, 1, 3, 2]
def baseStart_719208 : Nat := 118140960795 + 719208 * 2 ^ 59
def prefixEnd_719208 : Nat := 4983230072969 + 3 ^ 40 * 719208 * 2
def baseEnd_719208 : Nat := 369299394558927329092429

theorem tailTrace_719208 : CollatzResearch.WordTrace tailWord_719208 prefixEnd_719208 369299394558927329092429 := by
  unfold tailWord_719208
  simp only [CollatzResearch.WordTrace]
  refine ⟨13115835389219860896219139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17487780518959814528292185 13115835389219860896219139)
  ·
    refine ⟨19673753083829791344328709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13115835389219860896219139 19673753083829791344328709)
    ·
      refine ⟨3688828703218085877061633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19673753083829791344328709 3688828703218085877061633)
      ·
        refine ⟨2766621527413564407796225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3688828703218085877061633 2766621527413564407796225)
        ·
          refine ⟨2074966145560173305847169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2766621527413564407796225 2074966145560173305847169)
          ·
            refine ⟨1556224609170129979385377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2074966145560173305847169 1556224609170129979385377)
            ·
              refine ⟨1167168456877597484539033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1556224609170129979385377 1167168456877597484539033)
              ·
                refine ⟨875376342658198113404275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1167168456877597484539033 875376342658198113404275)
                ·
                  refine ⟨1313064513987297170106413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875376342658198113404275 1313064513987297170106413)
                  ·
                    refine ⟨492399192745236438789905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1313064513987297170106413 492399192745236438789905)
                    ·
                      refine ⟨369299394558927329092429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 492399192745236438789905 369299394558927329092429)
                      ·
                        rfl

theorem cell23_719208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_719208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719208 prefixEnd_719208 := by exact prefixLift 719208
  have htrace : WordTrace (prefixWord ++ tailWord_719208) baseStart_719208 baseEnd_719208 := by
    simpa [prefixWord, tailWord_719208, baseEnd_719208] using wordTrace_append hprefix tailTrace_719208
  have hstable : (prefixWord ++ tailWord_719208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719208).length < 2 ^ (prefixWord ++ tailWord_719208).sum := by decide
  have hdescent : baseEnd_719208 < baseStart_719208 := by decide
  rcases family_descends (prefixWord ++ tailWord_719208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719244 : List Nat := [2, 2, 1, 2, 1, 6, 1, 1, 7]
def baseStart_719244 : Nat := 118140960795 + 719244 * 2 ^ 59
def prefixEnd_719244 : Nat := 4983230072969 + 3 ^ 40 * 719244 * 2
def baseEnd_719244 : Nat := 41035319984721020915807

theorem tailTrace_719244 : CollatzResearch.WordTrace tailWord_719244 prefixEnd_719244 41035319984721020915807 := by
  unfold tailWord_719244
  simp only [CollatzResearch.WordTrace]
  refine ⟨13116491903154649970374393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17488655870872866627165857 13116491903154649970374393)
  ·
    refine ⟨9837368927365987477780795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13116491903154649970374393 9837368927365987477780795)
    ·
      refine ⟨14756053391048981216671193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9837368927365987477780795 14756053391048981216671193)
      ·
        refine ⟨11067040043286735912503395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14756053391048981216671193 11067040043286735912503395)
        ·
          refine ⟨16600560064930103868755093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11067040043286735912503395 16600560064930103868755093)
          ·
            refine ⟨778151253043598618847895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16600560064930103868755093 778151253043598618847895)
            ·
              refine ⟨1167226879565397928271843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778151253043598618847895 1167226879565397928271843)
              ·
                refine ⟨1750840319348096892407765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1167226879565397928271843 1750840319348096892407765)
                ·
                  refine ⟨41035319984721020915807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1750840319348096892407765 41035319984721020915807)
                  ·
                    rfl

theorem cell23_719244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 7].length) (baseStart_719244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719244 prefixEnd_719244 := by exact prefixLift 719244
  have htrace : WordTrace (prefixWord ++ tailWord_719244) baseStart_719244 baseEnd_719244 := by
    simpa [prefixWord, tailWord_719244, baseEnd_719244] using wordTrace_append hprefix tailTrace_719244
  have hstable : (prefixWord ++ tailWord_719244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719244).length < 2 ^ (prefixWord ++ tailWord_719244).sum := by decide
  have hdescent : baseEnd_719244 < baseStart_719244 := by decide
  rcases family_descends (prefixWord ++ tailWord_719244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719257 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 4, 5]
def baseStart_719257 : Nat := 118140960795 + 719257 * 2 ^ 59
def prefixEnd_719257 : Nat := 4983230072969 + 3 ^ 40 * 719257 * 2
def baseEnd_719257 : Nat := 123108185036999212459901

theorem tailTrace_719257 : CollatzResearch.WordTrace tailWord_719257 prefixEnd_719257 123108185036999212459901 := by
  unfold tailWord_719257
  simp only [CollatzResearch.WordTrace]
  refine ⟨26233457955262203160972025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17488971970174802107314683 26233457955262203160972025)
  ·
    refine ⟨19675093466446652370729019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26233457955262203160972025 19675093466446652370729019)
    ·
      refine ⟨29512640199669978556093529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19675093466446652370729019 29512640199669978556093529)
      ·
        refine ⟨22134480149752483917070147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29512640199669978556093529 22134480149752483917070147)
        ·
          refine ⟨33201720224628725875605221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22134480149752483917070147 33201720224628725875605221)
          ·
            refine ⟨6225322542117886101675979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33201720224628725875605221 6225322542117886101675979)
            ·
              refine ⟨9337983813176829152513969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6225322542117886101675979 9337983813176829152513969)
              ·
                refine ⟨7003487859882621864385477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9337983813176829152513969 7003487859882621864385477)
                ·
                  refine ⟨1313153973727991599572277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7003487859882621864385477 1313153973727991599572277)
                  ·
                    refine ⟨123108185036999212459901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1313153973727991599572277 123108185036999212459901)
                    ·
                      rfl

theorem cell23_719257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 5].length) (baseStart_719257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719257 prefixEnd_719257 := by exact prefixLift 719257
  have htrace : WordTrace (prefixWord ++ tailWord_719257) baseStart_719257 baseEnd_719257 := by
    simpa [prefixWord, tailWord_719257, baseEnd_719257] using wordTrace_append hprefix tailTrace_719257
  have hstable : (prefixWord ++ tailWord_719257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719257).length < 2 ^ (prefixWord ++ tailWord_719257).sum := by decide
  have hdescent : baseEnd_719257 < baseStart_719257 := by decide
  rcases family_descends (prefixWord ++ tailWord_719257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719307 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 4]
def baseStart_719307 : Nat := 118140960795 + 719307 * 2 ^ 59
def prefixEnd_719307 : Nat := 4983230072969 + 3 ^ 40 * 719307 * 2
def baseEnd_719307 : Nat := 369350229143722441754473

theorem tailTrace_719307 : CollatzResearch.WordTrace tailWord_719307 prefixEnd_719307 369350229143722441754473 := by
  unfold tailWord_719307
  simp only [CollatzResearch.WordTrace]
  refine ⟨26235281605081061700292175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17490187736720707800194783 26235281605081061700292175)
  ·
    refine ⟨39352922407621592550438263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26235281605081061700292175 39352922407621592550438263)
    ·
      refine ⟨59029383611432388825657395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39352922407621592550438263 59029383611432388825657395)
      ·
        refine ⟨88544075417148583238486093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59029383611432388825657395 88544075417148583238486093)
        ·
          refine ⟨33204028281430718714432285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88544075417148583238486093 33204028281430718714432285)
          ·
            refine ⟨12451510605536519517912107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33204028281430718714432285 12451510605536519517912107)
            ·
              refine ⟨18677265908304779276868161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12451510605536519517912107 18677265908304779276868161)
              ·
                refine ⟨14007949431228584457651121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18677265908304779276868161 14007949431228584457651121)
                ·
                  refine ⟨10505962073421438343238341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14007949431228584457651121 10505962073421438343238341)
                  ·
                    refine ⟨1969867888766519689357189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10505962073421438343238341 1969867888766519689357189)
                    ·
                      refine ⟨369350229143722441754473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1969867888766519689357189 369350229143722441754473)
                      ·
                        rfl

theorem cell23_719307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 4].length) (baseStart_719307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719307 prefixEnd_719307 := by exact prefixLift 719307
  have htrace : WordTrace (prefixWord ++ tailWord_719307) baseStart_719307 baseEnd_719307 := by
    simpa [prefixWord, tailWord_719307, baseEnd_719307] using wordTrace_append hprefix tailTrace_719307
  have hstable : (prefixWord ++ tailWord_719307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719307).length < 2 ^ (prefixWord ++ tailWord_719307).sum := by decide
  have hdescent : baseEnd_719307 < baseStart_719307 := by decide
  rcases family_descends (prefixWord ++ tailWord_719307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719331 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 3]
def baseStart_719331 : Nat := 118140960795 + 719331 * 2 ^ 59
def prefixEnd_719331 : Nat := 4983230072969 + 3 ^ 40 * 719331 * 2
def baseEnd_719331 : Nat := 369362552679430347854363

theorem tailTrace_719331 : CollatzResearch.WordTrace tailWord_719331 prefixEnd_719331 369362552679430347854363 := by
  unfold tailWord_719331
  simp only [CollatzResearch.WordTrace]
  refine ⟨26236156956994113799165847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17490771304662742532777231 26236156956994113799165847)
  ·
    refine ⟨39354235435491170698748771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26236156956994113799165847 39354235435491170698748771)
    ·
      refine ⟨59031353153236756048123157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39354235435491170698748771 59031353153236756048123157)
      ·
        refine ⟨2767094679057972939755773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59031353153236756048123157 2767094679057972939755773)
        ·
          refine ⟨1037660504646739852408415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2767094679057972939755773 1037660504646739852408415)
          ·
            refine ⟨1556490756970109778612623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037660504646739852408415 1556490756970109778612623)
            ·
              refine ⟨2334736135455164667918935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556490756970109778612623 2334736135455164667918935)
              ·
                refine ⟨3502104203182747001878403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2334736135455164667918935 3502104203182747001878403)
                ·
                  refine ⟨5253156304774120502817605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3502104203182747001878403 5253156304774120502817605)
                  ·
                    refine ⟨984966807145147594278301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5253156304774120502817605 984966807145147594278301)
                    ·
                      refine ⟨369362552679430347854363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 984966807145147594278301 369362552679430347854363)
                      ·
                        rfl

theorem cell23_719331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_719331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719331 prefixEnd_719331 := by exact prefixLift 719331
  have htrace : WordTrace (prefixWord ++ tailWord_719331) baseStart_719331 baseEnd_719331 := by
    simpa [prefixWord, tailWord_719331, baseEnd_719331] using wordTrace_append hprefix tailTrace_719331
  have hstable : (prefixWord ++ tailWord_719331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719331).length < 2 ^ (prefixWord ++ tailWord_719331).sum := by decide
  have hdescent : baseEnd_719331 < baseStart_719331 := by decide
  rcases family_descends (prefixWord ++ tailWord_719331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719338 : List Nat := [3, 1, 3, 1, 3, 1, 1, 5, 1, 4]
def baseStart_719338 : Nat := 118140960795 + 719338 * 2 ^ 59
def prefixEnd_719338 : Nat := 4983230072969 + 3 ^ 40 * 719338 * 2
def baseEnd_719338 : Nat := 123122049014670606822277

theorem tailTrace_719338 : CollatzResearch.WordTrace tailWord_719338 prefixEnd_719338 123122049014670606822277 := by
  unfold tailWord_719338
  simp only [CollatzResearch.WordTrace]
  refine ⟨6559103066992188498667667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17490941511979169329780445 6559103066992188498667667)
  ·
    refine ⟨9838654600488282748001501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6559103066992188498667667 9838654600488282748001501)
    ·
      refine ⟨3689495475183106030500563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9838654600488282748001501 3689495475183106030500563)
      ·
        refine ⟨5534243212774659045750845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3689495475183106030500563 5534243212774659045750845)
        ·
          refine ⟨2075341204790497142156567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5534243212774659045750845 2075341204790497142156567)
          ·
            refine ⟨3113011807185745713234851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2075341204790497142156567 3113011807185745713234851)
            ·
              refine ⟨4669517710778618569852277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3113011807185745713234851 4669517710778618569852277)
              ·
                refine ⟨437767285385495490923651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4669517710778618569852277 437767285385495490923651)
                ·
                  refine ⟨656650928078243236385477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 437767285385495490923651 656650928078243236385477)
                  ·
                    refine ⟨123122049014670606822277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 656650928078243236385477 123122049014670606822277)
                    ·
                      rfl

theorem cell23_719338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_719338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719338 prefixEnd_719338 := by exact prefixLift 719338
  have htrace : WordTrace (prefixWord ++ tailWord_719338) baseStart_719338 baseEnd_719338 := by
    simpa [prefixWord, tailWord_719338, baseEnd_719338] using wordTrace_append hprefix tailTrace_719338
  have hstable : (prefixWord ++ tailWord_719338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719338).length < 2 ^ (prefixWord ++ tailWord_719338).sum := by decide
  have hdescent : baseEnd_719338 < baseStart_719338 := by decide
  rcases family_descends (prefixWord ++ tailWord_719338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719371 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 1, 5, 2]
def baseStart_719371 : Nat := 118140960795 + 719371 * 2 ^ 59
def prefixEnd_719371 : Nat := 4983230072969 + 3 ^ 40 * 719371 * 2
def baseEnd_719371 : Nat := 369383091905610191354179

theorem tailTrace_719371 : CollatzResearch.WordTrace tailWord_719371 prefixEnd_719371 369383091905610191354179 := by
  unfold tailWord_719371
  simp only [CollatzResearch.WordTrace]
  refine ⟨26237615876849200630621967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17491743917899467087081311 26237615876849200630621967)
  ·
    refine ⟨39356423815273800945932951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26237615876849200630621967 39356423815273800945932951)
    ·
      refine ⟨59034635722910701418899427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39356423815273800945932951 59034635722910701418899427)
      ·
        refine ⟨88551953584366052128349141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59034635722910701418899427 88551953584366052128349141)
        ·
          refine ⟨2075436412133579346758183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 88551953584366052128349141 2075436412133579346758183)
          ·
            refine ⟨3113154618200369020137275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2075436412133579346758183 3113154618200369020137275)
            ·
              refine ⟨4669731927300553530205913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3113154618200369020137275 4669731927300553530205913)
              ·
                refine ⟨3502298945475415147654435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4669731927300553530205913 3502298945475415147654435)
                ·
                  refine ⟨5253448418213122721481653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3502298945475415147654435 5253448418213122721481653)
                  ·
                    refine ⟨492510789207480255138905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5253448418213122721481653 492510789207480255138905)
                    ·
                      refine ⟨369383091905610191354179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 492510789207480255138905 369383091905610191354179)
                      ·
                        rfl

theorem cell23_719371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 5, 2].length) (baseStart_719371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719371 prefixEnd_719371 := by exact prefixLift 719371
  have htrace : WordTrace (prefixWord ++ tailWord_719371) baseStart_719371 baseEnd_719371 := by
    simpa [prefixWord, tailWord_719371, baseEnd_719371] using wordTrace_append hprefix tailTrace_719371
  have hstable : (prefixWord ++ tailWord_719371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719371).length < 2 ^ (prefixWord ++ tailWord_719371).sum := by decide
  have hdescent : baseEnd_719371 < baseStart_719371 := by decide
  rcases family_descends (prefixWord ++ tailWord_719371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719381 : List Nat := [1, 3, 2, 1, 3, 1, 4, 2, 1, 5]
def baseStart_719381 : Nat := 118140960795 + 719381 * 2 ^ 59
def prefixEnd_719381 : Nat := 4983230072969 + 3 ^ 40 * 719381 * 2
def baseEnd_719381 : Nat := 123129408904051717409711

theorem tailTrace_719381 : CollatzResearch.WordTrace tailWord_719381 prefixEnd_719381 123129408904051717409711 := by
  unfold tailWord_719381
  simp only [CollatzResearch.WordTrace]
  refine ⟨26237980606812972338485997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17491987071208648225657331 26237980606812972338485997)
  ·
    refine ⟨9839242727554864626932249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26237980606812972338485997 9839242727554864626932249)
    ·
      refine ⟨7379432045666148470199187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9839242727554864626932249 7379432045666148470199187)
      ·
        refine ⟨11069148068499222705298781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7379432045666148470199187 11069148068499222705298781)
        ·
          refine ⟨4150930525687208514487043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11069148068499222705298781 4150930525687208514487043)
          ·
            refine ⟨6226395788530812771730565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4150930525687208514487043 6226395788530812771730565)
            ·
              refine ⟨1167449210349527394699481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6226395788530812771730565 1167449210349527394699481)
              ·
                refine ⟨875586907762145546024611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1167449210349527394699481 875586907762145546024611)
                ·
                  refine ⟨1313380361643218319036917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875586907762145546024611 1313380361643218319036917)
                  ·
                    refine ⟨123129408904051717409711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1313380361643218319036917 123129408904051717409711)
                    ·
                      rfl

theorem cell23_719381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_719381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719381 prefixEnd_719381 := by exact prefixLift 719381
  have htrace : WordTrace (prefixWord ++ tailWord_719381) baseStart_719381 baseEnd_719381 := by
    simpa [prefixWord, tailWord_719381, baseEnd_719381] using wordTrace_append hprefix tailTrace_719381
  have hstable : (prefixWord ++ tailWord_719381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719381).length < 2 ^ (prefixWord ++ tailWord_719381).sum := by decide
  have hdescent : baseEnd_719381 < baseStart_719381 := by decide
  rcases family_descends (prefixWord ++ tailWord_719381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719394 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_719394 : Nat := 118140960795 + 719394 * 2 ^ 59
def prefixEnd_719394 : Nat := 4983230072969 + 3 ^ 40 * 719394 * 2
def baseEnd_719394 : Nat := 123131633986887867122191

theorem tailTrace_719394 : CollatzResearch.WordTrace tailWord_719394 prefixEnd_719394 123131633986887867122191 := by
  unfold tailWord_719394
  simp only [CollatzResearch.WordTrace]
  refine ⟨6559613688941468889677309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17492303170510583705806157 6559613688941468889677309)
  ·
    refine ⟨2459855133353050833628991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6559613688941468889677309 2459855133353050833628991)
    ·
      refine ⟨3689782700029576250443487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2459855133353050833628991 3689782700029576250443487)
      ·
        refine ⟨5534674050044364375665231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3689782700029576250443487 5534674050044364375665231)
        ·
          refine ⟨8302011075066546563497847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5534674050044364375665231 8302011075066546563497847)
          ·
            refine ⟨12453016612599819845246771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8302011075066546563497847 12453016612599819845246771)
            ·
              refine ⟨18679524918899729767870157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12453016612599819845246771 18679524918899729767870157)
              ·
                refine ⟨7004821844587398662951309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18679524918899729767870157 7004821844587398662951309)
                ·
                  refine ⟨2626808191720274498606741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7004821844587398662951309 2626808191720274498606741)
                  ·
                    refine ⟨123131633986887867122191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2626808191720274498606741 123131633986887867122191)
                    ·
                      rfl

theorem cell23_719394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_719394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719394 prefixEnd_719394 := by exact prefixLift 719394
  have htrace : WordTrace (prefixWord ++ tailWord_719394) baseStart_719394 baseEnd_719394 := by
    simpa [prefixWord, tailWord_719394, baseEnd_719394] using wordTrace_append hprefix tailTrace_719394
  have hstable : (prefixWord ++ tailWord_719394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719394).length < 2 ^ (prefixWord ++ tailWord_719394).sum := by decide
  have hdescent : baseEnd_719394 < baseStart_719394 := by decide
  rcases family_descends (prefixWord ++ tailWord_719394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719395 : List Nat := [1, 1, 1, 4, 4, 1, 3, 3, 1, 1, 3]
def baseStart_719395 : Nat := 118140960795 + 719395 * 2 ^ 59
def prefixEnd_719395 : Nat := 4983230072969 + 3 ^ 40 * 719395 * 2
def baseEnd_719395 : Nat := 369395415441318097454069

theorem tailTrace_719395 : CollatzResearch.WordTrace tailWord_719395 prefixEnd_719395 369395415441318097454069 := by
  unfold tailWord_719395
  simp only [CollatzResearch.WordTrace]
  refine ⟨26238491228762252729495639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17492327485841501819663759 26238491228762252729495639)
  ·
    refine ⟨39357736843143379094243459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26238491228762252729495639 39357736843143379094243459)
    ·
      refine ⟨59036605264715068641365189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39357736843143379094243459 59036605264715068641365189)
      ·
        refine ⟨11069363487134075370255973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59036605264715068641365189 11069363487134075370255973)
        ·
          refine ⟨2075505653837639131922995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11069363487134075370255973 2075505653837639131922995)
          ·
            refine ⟨3113258480756458697884493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2075505653837639131922995 3113258480756458697884493)
            ·
              refine ⟨1167471930283672011706685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3113258480756458697884493 1167471930283672011706685)
              ·
                refine ⟨437801973856377004390007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1167471930283672011706685 437801973856377004390007)
                ·
                  refine ⟨656702960784565506585011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 437801973856377004390007 656702960784565506585011)
                  ·
                    refine ⟨985054441176848259877517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 656702960784565506585011 985054441176848259877517)
                    ·
                      refine ⟨369395415441318097454069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 985054441176848259877517 369395415441318097454069)
                      ·
                        rfl

theorem cell23_719395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 1, 1, 3].length) (baseStart_719395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719395 prefixEnd_719395 := by exact prefixLift 719395
  have htrace : WordTrace (prefixWord ++ tailWord_719395) baseStart_719395 baseEnd_719395 := by
    simpa [prefixWord, tailWord_719395, baseEnd_719395] using wordTrace_append hprefix tailTrace_719395
  have hstable : (prefixWord ++ tailWord_719395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719395).length < 2 ^ (prefixWord ++ tailWord_719395).sum := by decide
  have hdescent : baseEnd_719395 < baseStart_719395 := by decide
  rcases family_descends (prefixWord ++ tailWord_719395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719411 : List Nat := [1, 1, 1, 2, 4, 2, 2, 4, 2, 4]
def baseStart_719411 : Nat := 118140960795 + 719411 * 2 ^ 59
def prefixEnd_719411 : Nat := 4983230072969 + 3 ^ 40 * 719411 * 2
def baseEnd_719411 : Nat := 123134543710596678284665

theorem tailTrace_719411 : CollatzResearch.WordTrace tailWord_719411 prefixEnd_719411 123134543710596678284665 := by
  unfold tailWord_719411
  simp only [CollatzResearch.WordTrace]
  refine ⟨26239074796704287462078087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17492716531136191641385391 26239074796704287462078087)
  ·
    refine ⟨39358612195056431193117131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26239074796704287462078087 39358612195056431193117131)
    ·
      refine ⟨59037918292584646789675697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39358612195056431193117131 59037918292584646789675697)
      ·
        refine ⟨44278438719438485092256773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59037918292584646789675697 44278438719438485092256773)
        ·
          refine ⟨8302207259894715954798145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44278438719438485092256773 8302207259894715954798145)
          ·
            refine ⟨6226655444921036966098609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8302207259894715954798145 6226655444921036966098609)
            ·
              refine ⟨4669991583690777724573957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6226655444921036966098609 4669991583690777724573957)
              ·
                refine ⟨875623421942020823357617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4669991583690777724573957 875623421942020823357617)
                ·
                  refine ⟨656717566456515617518213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 875623421942020823357617 656717566456515617518213)
                  ·
                    refine ⟨123134543710596678284665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 656717566456515617518213 123134543710596678284665)
                    ·
                      rfl

theorem cell23_719411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 4].length) (baseStart_719411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719411 prefixEnd_719411 := by exact prefixLift 719411
  have htrace : WordTrace (prefixWord ++ tailWord_719411) baseStart_719411 baseEnd_719411 := by
    simpa [prefixWord, tailWord_719411, baseEnd_719411] using wordTrace_append hprefix tailTrace_719411
  have hstable : (prefixWord ++ tailWord_719411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719411).length < 2 ^ (prefixWord ++ tailWord_719411).sum := by decide
  have hdescent : baseEnd_719411 < baseStart_719411 := by decide
  rcases family_descends (prefixWord ++ tailWord_719411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719421 : List Nat := [1, 4, 1, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_719421 : Nat := 118140960795 + 719421 * 2 ^ 59
def prefixEnd_719421 : Nat := 4983230072969 + 3 ^ 40 * 719421 * 2
def baseEnd_719421 : Nat := 369408765938334995728949

theorem tailTrace_719421 : CollatzResearch.WordTrace tailWord_719421 prefixEnd_719421 369408765938334995728949 := by
  unfold tailWord_719421
  simp only [CollatzResearch.WordTrace]
  refine ⟨26239439526668059169942117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17492959684445372779961411 26239439526668059169942117)
  ·
    refine ⟨4919894911250261094364147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26239439526668059169942117 4919894911250261094364147)
    ·
      refine ⟨7379842366875391641546221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4919894911250261094364147 7379842366875391641546221)
      ·
        refine ⟨2767440887578271865579833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7379842366875391641546221 2767440887578271865579833)
        ·
          refine ⟨2075580665683703899184875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2767440887578271865579833 2075580665683703899184875)
          ·
            refine ⟨3113370998525555848777313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2075580665683703899184875 3113370998525555848777313)
            ·
              refine ⟨2335028248894166886582985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3113370998525555848777313 2335028248894166886582985)
              ·
                refine ⟨1751271186670625164937239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2335028248894166886582985 1751271186670625164937239)
                ·
                  refine ⟨2626906780005937747405859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751271186670625164937239 2626906780005937747405859)
                  ·
                    refine ⟨3940360170008906621108789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2626906780005937747405859 3940360170008906621108789)
                    ·
                      refine ⟨369408765938334995728949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3940360170008906621108789 369408765938334995728949)
                      ·
                        rfl

theorem cell23_719421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_719421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719421 prefixEnd_719421 := by exact prefixLift 719421
  have htrace : WordTrace (prefixWord ++ tailWord_719421) baseStart_719421 baseEnd_719421 := by
    simpa [prefixWord, tailWord_719421, baseEnd_719421] using wordTrace_append hprefix tailTrace_719421
  have hstable : (prefixWord ++ tailWord_719421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719421).length < 2 ^ (prefixWord ++ tailWord_719421).sum := by decide
  have hdescent : baseEnd_719421 < baseStart_719421 := by decide
  rcases family_descends (prefixWord ++ tailWord_719421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719438 : List Nat := [4, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3]
def baseStart_719438 : Nat := 118140960795 + 719438 * 2 ^ 59
def prefixEnd_719438 : Nat := 4983230072969 + 3 ^ 40 * 719438 * 2
def baseEnd_719438 : Nat := 369417495109461429216371

theorem tailTrace_719438 : CollatzResearch.WordTrace tailWord_719438 prefixEnd_719438 369417495109461429216371 := by
  unfold tailWord_719438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3280007445950808884163871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17493373045070980715540645 3280007445950808884163871)
  ·
    refine ⟨4920011168926213326245807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3280007445950808884163871 4920011168926213326245807)
    ·
      refine ⟨7380016753389319989368711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4920011168926213326245807 7380016753389319989368711)
      ·
        refine ⟨11070025130083979984053067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7380016753389319989368711 11070025130083979984053067)
        ·
          refine ⟨16605037695125969976079601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11070025130083979984053067 16605037695125969976079601)
          ·
            refine ⟨12453778271344477482059701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16605037695125969976079601 12453778271344477482059701)
            ·
              refine ⟨1167541712938544763943097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12453778271344477482059701 1167541712938544763943097)
              ·
                refine ⟨875656284703908572957323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1167541712938544763943097 875656284703908572957323)
                ·
                  refine ⟨1313484427055862859435985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875656284703908572957323 1313484427055862859435985)
                  ·
                    refine ⟨985113320291897144576989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1313484427055862859435985 985113320291897144576989)
                    ·
                      refine ⟨369417495109461429216371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 985113320291897144576989 369417495109461429216371)
                      ·
                        rfl

theorem cell23_719438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_719438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719438 prefixEnd_719438 := by exact prefixLift 719438
  have htrace : WordTrace (prefixWord ++ tailWord_719438) baseStart_719438 baseEnd_719438 := by
    simpa [prefixWord, tailWord_719438, baseEnd_719438] using wordTrace_append hprefix tailTrace_719438
  have hstable : (prefixWord ++ tailWord_719438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719438).length < 2 ^ (prefixWord ++ tailWord_719438).sum := by decide
  have hdescent : baseEnd_719438 < baseStart_719438 := by decide
  rcases family_descends (prefixWord ++ tailWord_719438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719458 : List Nat := [3, 3, 2, 3, 2, 10]
def baseStart_719458 : Nat := 118140960795 + 719458 * 2 ^ 59
def prefixEnd_719458 : Nat := 4983230072969 + 3 ^ 40 * 719458 * 2
def baseEnd_719458 : Nat := 1520278867170993213853

theorem tailTrace_719458 : CollatzResearch.WordTrace tailWord_719458 prefixEnd_719458 1520278867170993213853 := by
  unfold tailWord_719458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6560197256883503622259757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17493859351689342992692685 6560197256883503622259757)
  ·
    refine ⟨2460073971331313858347409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6560197256883503622259757 2460073971331313858347409)
    ·
      refine ⟨1845055478498485393760557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2460073971331313858347409 1845055478498485393760557)
      ·
        refine ⟨691895804436932022660209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1845055478498485393760557 691895804436932022660209)
        ·
          refine ⟨518921853327699016995157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 691895804436932022660209 518921853327699016995157)
          ·
            refine ⟨1520278867170993213853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 518921853327699016995157 1520278867170993213853)
            ·
              rfl

theorem cell23_719458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 10].length) (baseStart_719458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719458 prefixEnd_719458 := by exact prefixLift 719458
  have htrace : WordTrace (prefixWord ++ tailWord_719458) baseStart_719458 baseEnd_719458 := by
    simpa [prefixWord, tailWord_719458, baseEnd_719458] using wordTrace_append hprefix tailTrace_719458
  have hstable : (prefixWord ++ tailWord_719458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719458).length < 2 ^ (prefixWord ++ tailWord_719458).sum := by decide
  have hdescent : baseEnd_719458 < baseStart_719458 := by decide
  rcases family_descends (prefixWord ++ tailWord_719458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719468 : List Nat := [2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 3]
def baseStart_719468 : Nat := 118140960795 + 719468 * 2 ^ 59
def prefixEnd_719468 : Nat := 4983230072969 + 3 ^ 40 * 719468 * 2
def baseEnd_719468 : Nat := 369432899529096311841233

theorem tailTrace_719468 : CollatzResearch.WordTrace tailWord_719468 prefixEnd_719468 369432899529096311841233 := by
  unfold tailWord_719468
  simp only [CollatzResearch.WordTrace]
  refine ⟨13120576878748893098451529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17494102504998524131268705 13120576878748893098451529)
  ·
    refine ⟨9840432659061669823838647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13120576878748893098451529 9840432659061669823838647)
    ·
      refine ⟨14760648988592504735757971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9840432659061669823838647 14760648988592504735757971)
      ·
        refine ⟨22140973482888757103636957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14760648988592504735757971 22140973482888757103636957)
        ·
          refine ⟨8302865056083283913863859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22140973482888757103636957 8302865056083283913863859)
          ·
            refine ⟨12454297584124925870795789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8302865056083283913863859 12454297584124925870795789)
            ·
              refine ⟨4670361594046847201548421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12454297584124925870795789 4670361594046847201548421)
              ·
                refine ⟨875692798883783850290329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4670361594046847201548421 875692798883783850290329)
                ·
                  refine ⟨656769599162837887717747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 875692798883783850290329 656769599162837887717747)
                  ·
                    refine ⟨985154398744256831576621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 656769599162837887717747 985154398744256831576621)
                    ·
                      refine ⟨369432899529096311841233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 985154398744256831576621 369432899529096311841233)
                      ·
                        rfl

theorem cell23_719468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 3].length) (baseStart_719468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719468 prefixEnd_719468 := by exact prefixLift 719468
  have htrace : WordTrace (prefixWord ++ tailWord_719468) baseStart_719468 baseEnd_719468 := by
    simpa [prefixWord, tailWord_719468, baseEnd_719468] using wordTrace_append hprefix tailTrace_719468
  have hstable : (prefixWord ++ tailWord_719468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719468).length < 2 ^ (prefixWord ++ tailWord_719468).sum := by decide
  have hdescent : baseEnd_719468 < baseStart_719468 := by decide
  rcases family_descends (prefixWord ++ tailWord_719468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719469 : List Nat := [1, 5, 1, 1, 3, 1, 4, 2, 1, 2, 2]
def baseStart_719469 : Nat := 118140960795 + 719469 * 2 ^ 59
def prefixEnd_719469 : Nat := 4983230072969 + 3 ^ 40 * 719469 * 2
def baseEnd_719469 : Nat := 369433413009750807928729

theorem tailTrace_719469 : CollatzResearch.WordTrace tailWord_719469 prefixEnd_719469 369433413009750807928729 := by
  unfold tailWord_719469
  simp only [CollatzResearch.WordTrace]
  refine ⟨26241190230494163367689461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17494126820329442245126307 26241190230494163367689461)
  ·
    refine ⟨2460111584108827815720887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26241190230494163367689461 2460111584108827815720887)
    ·
      refine ⟨3690167376163241723581331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2460111584108827815720887 3690167376163241723581331)
      ·
        refine ⟨5535251064244862585371997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3690167376163241723581331 5535251064244862585371997)
        ·
          refine ⟨2075719149091823469514499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5535251064244862585371997 2075719149091823469514499)
          ·
            refine ⟨3113578723637735204271749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2075719149091823469514499 3113578723637735204271749)
            ·
              refine ⟨583796010682075350800953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3113578723637735204271749 583796010682075350800953)
              ·
                refine ⟨437847008011556513100715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 583796010682075350800953 437847008011556513100715)
                ·
                  refine ⟨656770512017334769651073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 437847008011556513100715 656770512017334769651073)
                  ·
                    refine ⟨492577884013001077238305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 656770512017334769651073 492577884013001077238305)
                    ·
                      refine ⟨369433413009750807928729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 492577884013001077238305 369433413009750807928729)
                      ·
                        rfl

theorem cell23_719469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_719469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719469 prefixEnd_719469 := by exact prefixLift 719469
  have htrace : WordTrace (prefixWord ++ tailWord_719469) baseStart_719469 baseEnd_719469 := by
    simpa [prefixWord, tailWord_719469, baseEnd_719469] using wordTrace_append hprefix tailTrace_719469
  have hstable : (prefixWord ++ tailWord_719469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719469).length < 2 ^ (prefixWord ++ tailWord_719469).sum := by decide
  have hdescent : baseEnd_719469 < baseStart_719469 := by decide
  rcases family_descends (prefixWord ++ tailWord_719469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719484 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 1, 8]
def baseStart_719484 : Nat := 118140960795 + 719484 * 2 ^ 59
def prefixEnd_719484 : Nat := 4983230072969 + 3 ^ 40 * 719484 * 2
def baseEnd_719484 : Nat := 123147038406522749747053

theorem tailTrace_719484 : CollatzResearch.WordTrace tailWord_719484 prefixEnd_719484 123147038406522749747053 := by
  unfold tailWord_719484
  simp only [CollatzResearch.WordTrace]
  refine ⟨13120868662719910464742753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17494491550293213952990337 13120868662719910464742753)
  ·
    refine ⟨9840651497039932848557065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13120868662719910464742753 9840651497039932848557065)
    ·
      refine ⟨7380488622779949636417799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9840651497039932848557065 7380488622779949636417799)
      ·
        refine ⟨11070732934169924454626699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7380488622779949636417799 11070732934169924454626699)
        ·
          refine ⟨16606099401254886681940049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11070732934169924454626699 16606099401254886681940049)
          ·
            refine ⟨12454574550941165011455037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16606099401254886681940049 12454574550941165011455037)
            ·
              refine ⟨4670465456602936879295639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12454574550941165011455037 4670465456602936879295639)
              ·
                refine ⟨7005698184904405318943459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4670465456602936879295639 7005698184904405318943459)
                ·
                  refine ⟨10508547277356607978415189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7005698184904405318943459 10508547277356607978415189)
                  ·
                    refine ⟨123147038406522749747053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10508547277356607978415189 123147038406522749747053)
                    ·
                      rfl

theorem cell23_719484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_719484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719484 prefixEnd_719484 := by exact prefixLift 719484
  have htrace : WordTrace (prefixWord ++ tailWord_719484) baseStart_719484 baseEnd_719484 := by
    simpa [prefixWord, tailWord_719484, baseEnd_719484] using wordTrace_append hprefix tailTrace_719484
  have hstable : (prefixWord ++ tailWord_719484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719484).length < 2 ^ (prefixWord ++ tailWord_719484).sum := by decide
  have hdescent : baseEnd_719484 < baseStart_719484 := by decide
  rcases family_descends (prefixWord ++ tailWord_719484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719665 : List Nat := [1, 2, 2, 3, 2, 1, 3, 2, 3, 1, 3]
def baseStart_719665 : Nat := 118140960795 + 719665 * 2 ^ 59
def prefixEnd_719665 : Nat := 4983230072969 + 3 ^ 40 * 719665 * 2
def baseEnd_719665 : Nat := 369534055218032041077827

theorem tailTrace_719665 : CollatzResearch.WordTrace tailWord_719665 prefixEnd_719665 369534055218032041077827 := by
  unfold tailWord_719665
  simp only [CollatzResearch.WordTrace]
  refine ⟨26248338937784088841824449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17498892625189392561216299 26248338937784088841824449)
  ·
    refine ⟨19686254203338066631368337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26248338937784088841824449 19686254203338066631368337)
    ·
      refine ⟨14764690652503549973526253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19686254203338066631368337 14764690652503549973526253)
      ·
        refine ⟨5536758994688831240072345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14764690652503549973526253 5536758994688831240072345)
        ·
          refine ⟨4152569246016623430054259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5536758994688831240072345 4152569246016623430054259)
          ·
            refine ⟨6228853869024935145081389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4152569246016623430054259 6228853869024935145081389)
            ·
              refine ⟨2335820200884350679405521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6228853869024935145081389 2335820200884350679405521)
              ·
                refine ⟨1751865150663263009554141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2335820200884350679405521 1751865150663263009554141)
                ·
                  refine ⟨656949431498723628582803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1751865150663263009554141 656949431498723628582803)
                  ·
                    refine ⟨985424147248085442874205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 656949431498723628582803 985424147248085442874205)
                    ·
                      refine ⟨369534055218032041077827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 985424147248085442874205 369534055218032041077827)
                      ·
                        rfl

theorem cell23_719665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_719665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719665 prefixEnd_719665 := by exact prefixLift 719665
  have htrace : WordTrace (prefixWord ++ tailWord_719665) baseStart_719665 baseEnd_719665 := by
    simpa [prefixWord, tailWord_719665, baseEnd_719665] using wordTrace_append hprefix tailTrace_719665
  have hstable : (prefixWord ++ tailWord_719665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719665).length < 2 ^ (prefixWord ++ tailWord_719665).sum := by decide
  have hdescent : baseEnd_719665 < baseStart_719665 := by decide
  rcases family_descends (prefixWord ++ tailWord_719665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719691 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 5]
def baseStart_719691 : Nat := 118140960795 + 719691 * 2 ^ 59
def prefixEnd_719691 : Nat := 4983230072969 + 3 ^ 40 * 719691 * 2
def baseEnd_719691 : Nat := 369547405715048939352707

theorem tailTrace_719691 : CollatzResearch.WordTrace tailWord_719691 prefixEnd_719691 369547405715048939352707 := by
  unfold tailWord_719691
  simp only [CollatzResearch.WordTrace]
  refine ⟨26249287235689895282270927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17499524823793263521513951 26249287235689895282270927)
  ·
    refine ⟨39373930853534842923406391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26249287235689895282270927 39373930853534842923406391)
    ·
      refine ⟨59060896280302264385109587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39373930853534842923406391 59060896280302264385109587)
      ·
        refine ⟨88591344420453396577664381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59060896280302264385109587 88591344420453396577664381)
        ·
          refine ⟨33221754157670023716624143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88591344420453396577664381 33221754157670023716624143)
          ·
            refine ⟨49832631236505035574936215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33221754157670023716624143 49832631236505035574936215)
            ·
              refine ⟨74748946854757553362404323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49832631236505035574936215 74748946854757553362404323)
              ·
                refine ⟨112123420282136330043606485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74748946854757553362404323 112123420282136330043606485)
                ·
                  refine ⟨2627892662862570235397027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 112123420282136330043606485 2627892662862570235397027)
                  ·
                    refine ⟨3941838994293855353095541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2627892662862570235397027 3941838994293855353095541)
                    ·
                      refine ⟨369547405715048939352707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3941838994293855353095541 369547405715048939352707)
                      ·
                        rfl

theorem cell23_719691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 5].length) (baseStart_719691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719691 prefixEnd_719691 := by exact prefixLift 719691
  have htrace : WordTrace (prefixWord ++ tailWord_719691) baseStart_719691 baseEnd_719691 := by
    simpa [prefixWord, tailWord_719691, baseEnd_719691] using wordTrace_append hprefix tailTrace_719691
  have hstable : (prefixWord ++ tailWord_719691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719691).length < 2 ^ (prefixWord ++ tailWord_719691).sum := by decide
  have hdescent : baseEnd_719691 < baseStart_719691 := by decide
  rcases family_descends (prefixWord ++ tailWord_719691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719711 : List Nat := [1, 1, 2, 3, 1, 3, 2, 10]
def baseStart_719711 : Nat := 118140960795 + 719711 * 2 ^ 59
def prefixEnd_719711 : Nat := 4983230072969 + 3 ^ 40 * 719711 * 2
def baseEnd_719711 : Nat := 13687321308449587448245

theorem tailTrace_719711 : CollatzResearch.WordTrace tailWord_719711 prefixEnd_719711 13687321308449587448245 := by
  unfold tailWord_719711
  simp only [CollatzResearch.WordTrace]
  refine ⟨26250016695617438697998987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17500011130411625798665991 26250016695617438697998987)
  ·
    refine ⟨39375025043426158046998481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26250016695617438697998987 39375025043426158046998481)
    ·
      refine ⟨29531268782569618535248861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39375025043426158046998481 29531268782569618535248861)
      ·
        refine ⟨11074225793463606950718323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29531268782569618535248861 11074225793463606950718323)
        ·
          refine ⟨16611338690195410426077485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11074225793463606950718323 16611338690195410426077485)
          ·
            refine ⟨6229252008823278909779057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16611338690195410426077485 6229252008823278909779057)
            ·
              refine ⟨4671939006617459182334293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6229252008823278909779057 4671939006617459182334293)
              ·
                refine ⟨13687321308449587448245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4671939006617459182334293 13687321308449587448245)
                ·
                  rfl

theorem cell23_719711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 10].length) (baseStart_719711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719711 prefixEnd_719711 := by exact prefixLift 719711
  have htrace : WordTrace (prefixWord ++ tailWord_719711) baseStart_719711 baseEnd_719711 := by
    simpa [prefixWord, tailWord_719711, baseEnd_719711] using wordTrace_append hprefix tailTrace_719711
  have hstable : (prefixWord ++ tailWord_719711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719711).length < 2 ^ (prefixWord ++ tailWord_719711).sum := by decide
  have hdescent : baseEnd_719711 < baseStart_719711 := by decide
  rcases family_descends (prefixWord ++ tailWord_719711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719715 : List Nat := [1, 1, 1, 5, 3, 3, 1, 1, 1, 6]
def baseStart_719715 : Nat := 118140960795 + 719715 * 2 ^ 59
def prefixEnd_719715 : Nat := 4983230072969 + 3 ^ 40 * 719715 * 2
def baseEnd_719715 : Nat := 123186576416918948484199

theorem tailTrace_719715 : CollatzResearch.WordTrace tailWord_719715 prefixEnd_719715 123186576416918948484199 := by
  unfold tailWord_719715
  simp only [CollatzResearch.WordTrace]
  refine ⟨26250162587602947381144599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17500108391735298254096399 26250162587602947381144599)
  ·
    refine ⟨39375243881404421071716899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26250162587602947381144599 39375243881404421071716899)
    ·
      refine ⟨59062865822106631607575349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39375243881404421071716899 59062865822106631607575349)
      ·
        refine ⟨5537143670822496713210189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59062865822106631607575349 5537143670822496713210189)
        ·
          refine ⟨2076428876558436267453821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5537143670822496713210189 2076428876558436267453821)
          ·
            refine ⟨778660828709413600295183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2076428876558436267453821 778660828709413600295183)
            ·
              refine ⟨1167991243064120400442775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778660828709413600295183 1167991243064120400442775)
              ·
                refine ⟨1751986864596180600664163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1167991243064120400442775 1751986864596180600664163)
                ·
                  refine ⟨2627980296894270900996245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751986864596180600664163 2627980296894270900996245)
                  ·
                    refine ⟨123186576416918948484199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2627980296894270900996245 123186576416918948484199)
                    ·
                      rfl

theorem cell23_719715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 6].length) (baseStart_719715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719715 prefixEnd_719715 := by exact prefixLift 719715
  have htrace : WordTrace (prefixWord ++ tailWord_719715) baseStart_719715 baseEnd_719715 := by
    simpa [prefixWord, tailWord_719715, baseEnd_719715] using wordTrace_append hprefix tailTrace_719715
  have hstable : (prefixWord ++ tailWord_719715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719715).length < 2 ^ (prefixWord ++ tailWord_719715).sum := by decide
  have hdescent : baseEnd_719715 < baseStart_719715 := by decide
  rcases family_descends (prefixWord ++ tailWord_719715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719728 : List Nat := [2, 1, 1, 1, 4, 1, 6, 7]
def baseStart_719728 : Nat := 118140960795 + 719728 * 2 ^ 59
def prefixEnd_719728 : Nat := 4983230072969 + 3 ^ 40 * 719728 * 2
def baseEnd_719728 : Nat := 13687644611083899799631

theorem tailTrace_719728 : CollatzResearch.WordTrace tailWord_719728 prefixEnd_719728 13687644611083899799631 := by
  unfold tailWord_719728
  simp only [CollatzResearch.WordTrace]
  refine ⟨13125318368277925300683919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17500424491037233734245225 13125318368277925300683919)
  ·
    refine ⟨19687977552416887951025879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13125318368277925300683919 19687977552416887951025879)
    ·
      refine ⟨29531966328625331926538819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19687977552416887951025879 29531966328625331926538819)
      ·
        refine ⟨44297949492937997889808229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29531966328625331926538819 44297949492937997889808229)
        ·
          refine ⟨8305865529925874604339043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44297949492937997889808229 8305865529925874604339043)
          ·
            refine ⟨12458798294888811906508565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8305865529925874604339043 12458798294888811906508565)
            ·
              refine ⟨584006170072913058117589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12458798294888811906508565 584006170072913058117589)
              ·
                refine ⟨13687644611083899799631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 584006170072913058117589 13687644611083899799631)
                ·
                  rfl

theorem cell23_719728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 7].length) (baseStart_719728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719728 prefixEnd_719728 := by exact prefixLift 719728
  have htrace : WordTrace (prefixWord ++ tailWord_719728) baseStart_719728 baseEnd_719728 := by
    simpa [prefixWord, tailWord_719728, baseEnd_719728] using wordTrace_append hprefix tailTrace_719728
  have hstable : (prefixWord ++ tailWord_719728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719728).length < 2 ^ (prefixWord ++ tailWord_719728).sum := by decide
  have hdescent : baseEnd_719728 < baseStart_719728 := by decide
  rcases family_descends (prefixWord ++ tailWord_719728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719738 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3]
def baseStart_719738 : Nat := 118140960795 + 719738 * 2 ^ 59
def prefixEnd_719738 : Nat := 4983230072969 + 3 ^ 40 * 719738 * 2
def baseEnd_719738 : Nat := 369571539305810255464991

theorem tailTrace_719738 : CollatzResearch.WordTrace tailWord_719738 prefixEnd_719738 369571539305810255464991 := by
  unfold tailWord_719738
  simp only [CollatzResearch.WordTrace]
  refine ⟨6562750366629905577307967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17500667644346414872821245 6562750366629905577307967)
  ·
    refine ⟨9844125549944858365961951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6562750366629905577307967 9844125549944858365961951)
    ·
      refine ⟨14766188324917287548942927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9844125549944858365961951 14766188324917287548942927)
      ·
        refine ⟨22149282487375931323414391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14766188324917287548942927 22149282487375931323414391)
        ·
          refine ⟨33223923731063896985121587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22149282487375931323414391 33223923731063896985121587)
          ·
            refine ⟨49835885596595845477682381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33223923731063896985121587 49835885596595845477682381)
            ·
              refine ⟨18688457098723442054130893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49835885596595845477682381 18688457098723442054130893)
              ·
                refine ⟨7008171412021290770299085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18688457098723442054130893 7008171412021290770299085)
                ·
                  refine ⟨2628064279507984038862157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7008171412021290770299085 2628064279507984038862157)
                  ·
                    refine ⟨985524104815494014573309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2628064279507984038862157 985524104815494014573309)
                    ·
                      refine ⟨369571539305810255464991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 985524104815494014573309 369571539305810255464991)
                      ·
                        rfl

theorem cell23_719738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_719738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719738 prefixEnd_719738 := by exact prefixLift 719738
  have htrace : WordTrace (prefixWord ++ tailWord_719738) baseStart_719738 baseEnd_719738 := by
    simpa [prefixWord, tailWord_719738, baseEnd_719738] using wordTrace_append hprefix tailTrace_719738
  have hstable : (prefixWord ++ tailWord_719738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719738).length < 2 ^ (prefixWord ++ tailWord_719738).sum := by decide
  have hdescent : baseEnd_719738 < baseStart_719738 := by decide
  rcases family_descends (prefixWord ++ tailWord_719738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719739 : List Nat := [1, 1, 1, 1, 1, 5, 5, 3, 1, 2, 2]
def baseStart_719739 : Nat := 118140960795 + 719739 * 2 ^ 59
def prefixEnd_719739 : Nat := 4983230072969 + 3 ^ 40 * 719739 * 2
def baseEnd_719739 : Nat := 369572052786464751552487

theorem tailTrace_719739 : CollatzResearch.WordTrace tailWord_719739 prefixEnd_719739 369572052786464751552487 := by
  unfold tailWord_719739
  simp only [CollatzResearch.WordTrace]
  refine ⟨26251037939515999480018271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17500691959677332986678847 26251037939515999480018271)
  ·
    refine ⟨39376556909273999220027407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26251037939515999480018271 39376556909273999220027407)
    ·
      refine ⟨59064835363910998830041111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39376556909273999220027407 59064835363910998830041111)
      ·
        refine ⟨88597253045866498245061667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59064835363910998830041111 88597253045866498245061667)
        ·
          refine ⟨132895879568799747367592501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88597253045866498245061667 132895879568799747367592501)
          ·
            refine ⟨12458988709574976315711797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132895879568799747367592501 12458988709574976315711797)
            ·
              refine ⟨1168030191522654029597981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12458988709574976315711797 1168030191522654029597981)
              ·
                refine ⟨438011321820995261099243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1168030191522654029597981 438011321820995261099243)
                ·
                  refine ⟨657016982731492891648865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438011321820995261099243 657016982731492891648865)
                  ·
                    refine ⟨492762737048619668736649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 657016982731492891648865 492762737048619668736649)
                    ·
                      refine ⟨369572052786464751552487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 492762737048619668736649 369572052786464751552487)
                      ·
                        rfl

theorem cell23_719739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 1, 2, 2].length) (baseStart_719739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719739 prefixEnd_719739 := by exact prefixLift 719739
  have htrace : WordTrace (prefixWord ++ tailWord_719739) baseStart_719739 baseEnd_719739 := by
    simpa [prefixWord, tailWord_719739, baseEnd_719739] using wordTrace_append hprefix tailTrace_719739
  have hstable : (prefixWord ++ tailWord_719739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719739).length < 2 ^ (prefixWord ++ tailWord_719739).sum := by decide
  have hdescent : baseEnd_719739 < baseStart_719739 := by decide
  rcases family_descends (prefixWord ++ tailWord_719739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719755 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 4, 1, 3]
def baseStart_719755 : Nat := 118140960795 + 719755 * 2 ^ 59
def prefixEnd_719755 : Nat := 4983230072969 + 3 ^ 40 * 719755 * 2
def baseEnd_719755 : Nat := 369580268476936688952413

theorem tailTrace_719755 : CollatzResearch.WordTrace tailWord_719755 prefixEnd_719755 369580268476936688952413 := by
  unfold tailWord_719755
  simp only [CollatzResearch.WordTrace]
  refine ⟨26251621507458034212600719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17501081004972022808400479 26251621507458034212600719)
  ·
    refine ⟨39377432261187051318901079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26251621507458034212600719 39377432261187051318901079)
    ·
      refine ⟨59066148391780576978351619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39377432261187051318901079 59066148391780576978351619)
      ·
        refine ⟨88599222587670865467527429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59066148391780576978351619 88599222587670865467527429)
        ·
          refine ⟨16612354235188287275161393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88599222587670865467527429 16612354235188287275161393)
          ·
            refine ⟨12459265676391215456371045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16612354235188287275161393 12459265676391215456371045)
            ·
              refine ⟨2336112314323352898069571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12459265676391215456371045 2336112314323352898069571)
              ·
                refine ⟨3504168471485029347104357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2336112314323352898069571 3504168471485029347104357)
                ·
                  refine ⟨657031588403443002582067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3504168471485029347104357 657031588403443002582067)
                  ·
                    refine ⟨985547382605164503873101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 657031588403443002582067 985547382605164503873101)
                    ·
                      refine ⟨369580268476936688952413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 985547382605164503873101 369580268476936688952413)
                      ·
                        rfl

theorem cell23_719755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 1, 3].length) (baseStart_719755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719755 prefixEnd_719755 := by exact prefixLift 719755
  have htrace : WordTrace (prefixWord ++ tailWord_719755) baseStart_719755 baseEnd_719755 := by
    simpa [prefixWord, tailWord_719755, baseEnd_719755] using wordTrace_append hprefix tailTrace_719755
  have hstable : (prefixWord ++ tailWord_719755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719755).length < 2 ^ (prefixWord ++ tailWord_719755).sum := by decide
  have hdescent : baseEnd_719755 < baseStart_719755 := by decide
  rcases family_descends (prefixWord ++ tailWord_719755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719766 : List Nat := [5, 3, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_719766 : Nat := 118140960795 + 719766 * 2 ^ 59
def prefixEnd_719766 : Nat := 4983230072969 + 3 ^ 40 * 719766 * 2
def baseEnd_719766 : Nat := 123195305588045381971621

theorem tailTrace_719766 : CollatzResearch.WordTrace tailWord_719766 prefixEnd_719766 123195305588045381971621 := by
  unfold tailWord_719766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1640751419401136443203197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17501348473612122060834101 1640751419401136443203197)
  ·
    refine ⟨615281782275426166201199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1640751419401136443203197 615281782275426166201199)
    ·
      refine ⟨922922673413139249301799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 615281782275426166201199 922922673413139249301799)
      ·
        refine ⟨1384384010119708873952699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 922922673413139249301799 1384384010119708873952699)
        ·
          refine ⟨2076576015179563310929049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1384384010119708873952699 2076576015179563310929049)
          ·
            refine ⟨1557432011384672483196787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2076576015179563310929049 1557432011384672483196787)
            ·
              refine ⟨2336148017077008724795181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1557432011384672483196787 2336148017077008724795181)
              ·
                refine ⟨876055506403878271798193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2336148017077008724795181 876055506403878271798193)
                ·
                  refine ⟨657041629802908703848645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 876055506403878271798193 657041629802908703848645)
                  ·
                    refine ⟨123195305588045381971621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 657041629802908703848645 123195305588045381971621)
                    ·
                      rfl

theorem cell23_719766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_719766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719766 prefixEnd_719766 := by exact prefixLift 719766
  have htrace : WordTrace (prefixWord ++ tailWord_719766) baseStart_719766 baseEnd_719766 := by
    simpa [prefixWord, tailWord_719766, baseEnd_719766] using wordTrace_append hprefix tailTrace_719766
  have hstable : (prefixWord ++ tailWord_719766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719766).length < 2 ^ (prefixWord ++ tailWord_719766).sum := by decide
  have hdescent : baseEnd_719766 < baseStart_719766 := by decide
  rcases family_descends (prefixWord ++ tailWord_719766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719789 : List Nat := [1, 5, 2, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_719789 : Nat := 118140960795 + 719789 * 2 ^ 59
def prefixEnd_719789 : Nat := 4983230072969 + 3 ^ 40 * 719789 * 2
def baseEnd_719789 : Nat := 369597726819189555927257

theorem tailTrace_719789 : CollatzResearch.WordTrace tailWord_719789 prefixEnd_719789 369597726819189555927257 := by
  unfold tailWord_719789
  simp only [CollatzResearch.WordTrace]
  refine ⟨26252861589334858019338421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17501907726223238679558947 26252861589334858019338421)
  ·
    refine ⟨2461205774000142939312977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26252861589334858019338421 2461205774000142939312977)
    ·
      refine ⟨1845904330500107204484733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2461205774000142939312977 1845904330500107204484733)
      ·
        refine ⟨692214123937540201681775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1845904330500107204484733 692214123937540201681775)
        ·
          refine ⟨1038321185906310302522663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 692214123937540201681775 1038321185906310302522663)
          ·
            refine ⟨1557481778859465453783995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038321185906310302522663 1557481778859465453783995)
            ·
              refine ⟨2336222668289198180675993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1557481778859465453783995 2336222668289198180675993)
              ·
                refine ⟨1752167001216898635506995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2336222668289198180675993 1752167001216898635506995)
                ·
                  refine ⟨2628250501825347953260493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752167001216898635506995 2628250501825347953260493)
                  ·
                    refine ⟨985593938184505482472685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2628250501825347953260493 985593938184505482472685)
                    ·
                      refine ⟨369597726819189555927257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 985593938184505482472685 369597726819189555927257)
                      ·
                        rfl

theorem cell23_719789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_719789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719789 prefixEnd_719789 := by exact prefixLift 719789
  have htrace : WordTrace (prefixWord ++ tailWord_719789) baseStart_719789 baseEnd_719789 := by
    simpa [prefixWord, tailWord_719789, baseEnd_719789] using wordTrace_append hprefix tailTrace_719789
  have hstable : (prefixWord ++ tailWord_719789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719789).length < 2 ^ (prefixWord ++ tailWord_719789).sum := by decide
  have hdescent : baseEnd_719789 < baseStart_719789 := by decide
  rcases family_descends (prefixWord ++ tailWord_719789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719818 : List Nat := [3, 1, 2, 1, 2, 1, 1, 5, 7]
def baseStart_719818 : Nat := 118140960795 + 719818 * 2 ^ 59
def prefixEnd_719818 : Nat := 4983230072969 + 3 ^ 40 * 719818 * 2
def baseEnd_719818 : Nat := 41068068639796660273847

theorem tailTrace_719818 : CollatzResearch.WordTrace tailWord_719818 prefixEnd_719818 41068068639796660273847 := by
  unfold tailWord_719818
  simp only [CollatzResearch.WordTrace]
  refine ⟨6563479826557448993036027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17502612870819863981429405 6563479826557448993036027)
  ·
    refine ⟨9845219739836173489554041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6563479826557448993036027 9845219739836173489554041)
    ·
      refine ⟨7383914804877130117165531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9845219739836173489554041 7383914804877130117165531)
      ·
        refine ⟨11075872207315695175748297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7383914804877130117165531 11075872207315695175748297)
        ·
          refine ⟨8306904155486771381811223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11075872207315695175748297 8306904155486771381811223)
          ·
            refine ⟨12460356233230157072716835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8306904155486771381811223 12460356233230157072716835)
            ·
              refine ⟨18690534349845235609075253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12460356233230157072716835 18690534349845235609075253)
              ·
                refine ⟨1752237595297990838350805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18690534349845235609075253 1752237595297990838350805)
                ·
                  refine ⟨41068068639796660273847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1752237595297990838350805 41068068639796660273847)
                  ·
                    rfl

theorem cell23_719818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 7].length) (baseStart_719818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719818 prefixEnd_719818 := by exact prefixLift 719818
  have htrace : WordTrace (prefixWord ++ tailWord_719818) baseStart_719818 baseEnd_719818 := by
    simpa [prefixWord, tailWord_719818, baseEnd_719818] using wordTrace_append hprefix tailTrace_719818
  have hstable : (prefixWord ++ tailWord_719818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719818).length < 2 ^ (prefixWord ++ tailWord_719818).sum := by decide
  have hdescent : baseEnd_719818 < baseStart_719818 := by decide
  rcases family_descends (prefixWord ++ tailWord_719818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719829 : List Nat := [1, 3, 2, 3, 3, 1, 2, 1, 1, 4, 2]
def baseStart_719829 : Nat := 118140960795 + 719829 * 2 ^ 59
def prefixEnd_719829 : Nat := 4983230072969 + 3 ^ 40 * 719829 * 2
def baseEnd_719829 : Nat := 369618266045369399427073

theorem tailTrace_719829 : CollatzResearch.WordTrace tailWord_719829 prefixEnd_719829 369618266045369399427073 := by
  unfold tailWord_719829
  simp only [CollatzResearch.WordTrace]
  refine ⟨26254320509189944850794541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17502880339459963233863027 26254320509189944850794541)
  ·
    refine ⟨9845370190946229319047953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26254320509189944850794541 9845370190946229319047953)
    ·
      refine ⟨7384027643209671989285965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9845370190946229319047953 7384027643209671989285965)
      ·
        refine ⟨2769010366203626995982237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7384027643209671989285965 2769010366203626995982237)
        ·
          refine ⟨1038378887326360123493339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2769010366203626995982237 1038378887326360123493339)
          ·
            refine ⟨1557568330989540185240009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038378887326360123493339 1557568330989540185240009)
            ·
              refine ⟨1168176248242155138930007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1557568330989540185240009 1168176248242155138930007)
              ·
                refine ⟨1752264372363232708395011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168176248242155138930007 1752264372363232708395011)
                ·
                  refine ⟨2628396558544849062592517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752264372363232708395011 2628396558544849062592517)
                  ·
                    refine ⟨492824354727159199236097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2628396558544849062592517 492824354727159199236097)
                    ·
                      refine ⟨369618266045369399427073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 492824354727159199236097 369618266045369399427073)
                      ·
                        rfl

theorem cell23_719829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_719829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719829 prefixEnd_719829 := by exact prefixLift 719829
  have htrace : WordTrace (prefixWord ++ tailWord_719829) baseStart_719829 baseEnd_719829 := by
    simpa [prefixWord, tailWord_719829, baseEnd_719829] using wordTrace_append hprefix tailTrace_719829
  have hstable : (prefixWord ++ tailWord_719829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719829).length < 2 ^ (prefixWord ++ tailWord_719829).sum := by decide
  have hdescent : baseEnd_719829 < baseStart_719829 := by decide
  rcases family_descends (prefixWord ++ tailWord_719829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719862 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_719862 : Nat := 118140960795 + 719862 * 2 ^ 59
def prefixEnd_719862 : Nat := 4983230072969 + 3 ^ 40 * 719862 * 2
def baseEnd_719862 : Nat := 369635210906967770314421

theorem tailTrace_719862 : CollatzResearch.WordTrace tailWord_719862 prefixEnd_719862 369635210906967770314421 := by
  unfold tailWord_719862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1640970257379399467921615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17503682745380260991163893 1640970257379399467921615)
  ·
    refine ⟨2461455386069099201882423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1640970257379399467921615 2461455386069099201882423)
    ·
      refine ⟨3692183079103648802823635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2461455386069099201882423 3692183079103648802823635)
      ·
        refine ⟨5538274618655473204235453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3692183079103648802823635 5538274618655473204235453)
        ·
          refine ⟨2076852981995802451588295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5538274618655473204235453 2076852981995802451588295)
          ·
            refine ⟨3115279472993703677382443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2076852981995802451588295 3115279472993703677382443)
            ·
              refine ⟨4672919209490555516073665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3115279472993703677382443 4672919209490555516073665)
              ·
                refine ⟨3504689407117916637055249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4672919209490555516073665 3504689407117916637055249)
                ·
                  refine ⟨2628517055338437477791437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3504689407117916637055249 2628517055338437477791437)
                  ·
                    refine ⟨985693895751914054171789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2628517055338437477791437 985693895751914054171789)
                    ·
                      refine ⟨369635210906967770314421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 985693895751914054171789 369635210906967770314421)
                      ·
                        rfl

theorem cell23_719862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_719862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719862 prefixEnd_719862 := by exact prefixLift 719862
  have htrace : WordTrace (prefixWord ++ tailWord_719862) baseStart_719862 baseEnd_719862 := by
    simpa [prefixWord, tailWord_719862, baseEnd_719862] using wordTrace_append hprefix tailTrace_719862
  have hstable : (prefixWord ++ tailWord_719862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719862).length < 2 ^ (prefixWord ++ tailWord_719862).sum := by decide
  have hdescent : baseEnd_719862 < baseStart_719862 := by decide
  rcases family_descends (prefixWord ++ tailWord_719862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719922 : List Nat := [3, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3]
def baseStart_719922 : Nat := 118140960795 + 719922 * 2 ^ 59
def prefixEnd_719922 : Nat := 4983230072969 + 3 ^ 40 * 719922 * 2
def baseEnd_719922 : Nat := 369666019746237535564145

theorem tailTrace_719922 : CollatzResearch.WordTrace tailWord_719922 prefixEnd_719922 369666019746237535564145 := by
  unfold tailWord_719922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6564428124463255433482505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17505141665235347822620013 6564428124463255433482505)
  ·
    refine ⟨4923321093347441575111879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6564428124463255433482505 4923321093347441575111879)
    ·
      refine ⟨7384981640021162362667819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4923321093347441575111879 7384981640021162362667819)
      ·
        refine ⟨11077472460031743544001729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7384981640021162362667819 11077472460031743544001729)
        ·
          refine ⟨8308104345023807658001297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11077472460031743544001729 8308104345023807658001297)
          ·
            refine ⟨6231078258767855743500973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8308104345023807658001297 6231078258767855743500973)
            ·
              refine ⟨2336654347037945903812865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6231078258767855743500973 2336654347037945903812865)
              ·
                refine ⟨1752490760278459427859649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2336654347037945903812865 1752490760278459427859649)
                ·
                  refine ⟨1314368070208844570894737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1752490760278459427859649 1314368070208844570894737)
                  ·
                    refine ⟨985776052656633428171053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1314368070208844570894737 985776052656633428171053)
                    ·
                      refine ⟨369666019746237535564145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 985776052656633428171053 369666019746237535564145)
                      ·
                        rfl

theorem cell23_719922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_719922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719922 prefixEnd_719922 := by exact prefixLift 719922
  have htrace : WordTrace (prefixWord ++ tailWord_719922) baseStart_719922 baseEnd_719922 := by
    simpa [prefixWord, tailWord_719922, baseEnd_719922] using wordTrace_append hprefix tailTrace_719922
  have hstable : (prefixWord ++ tailWord_719922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719922).length < 2 ^ (prefixWord ++ tailWord_719922).sum := by decide
  have hdescent : baseEnd_719922 < baseStart_719922 := by decide
  rcases family_descends (prefixWord ++ tailWord_719922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719925 : List Nat := [1, 3, 3, 1, 1, 1, 1, 6, 6]
def baseStart_719925 : Nat := 118140960795 + 719925 * 2 ^ 59
def prefixEnd_719925 : Nat := 4983230072969 + 3 ^ 40 * 719925 * 2
def baseEnd_719925 : Nat := 41074173354244558202959

theorem tailTrace_719925 : CollatzResearch.WordTrace tailWord_719925 prefixEnd_719925 41074173354244558202959 := by
  unfold tailWord_719925
  simp only [CollatzResearch.WordTrace]
  refine ⟨26257821916842153246289229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17505214611228102164192819 26257821916842153246289229)
  ·
    refine ⟨9846683218815807467358461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26257821916842153246289229 9846683218815807467358461)
    ·
      refine ⟨3692506207055927800259423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9846683218815807467358461 3692506207055927800259423)
      ·
        refine ⟨5538759310583891700389135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3692506207055927800259423 5538759310583891700389135)
        ·
          refine ⟨8308138965875837550583703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5538759310583891700389135 8308138965875837550583703)
          ·
            refine ⟨12462208448813756325875555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8308138965875837550583703 12462208448813756325875555)
            ·
              refine ⟨18693312673220634488813333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12462208448813756325875555 18693312673220634488813333)
              ·
                refine ⟨876249031557217241663125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18693312673220634488813333 876249031557217241663125)
                ·
                  refine ⟨41074173354244558202959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 876249031557217241663125 41074173354244558202959)
                  ·
                    rfl

theorem cell23_719925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 6].length) (baseStart_719925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719925 prefixEnd_719925 := by exact prefixLift 719925
  have htrace : WordTrace (prefixWord ++ tailWord_719925) baseStart_719925 baseEnd_719925 := by
    simpa [prefixWord, tailWord_719925, baseEnd_719925] using wordTrace_append hprefix tailTrace_719925
  have hstable : (prefixWord ++ tailWord_719925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719925).length < 2 ^ (prefixWord ++ tailWord_719925).sum := by decide
  have hdescent : baseEnd_719925 < baseStart_719925 := by decide
  rcases family_descends (prefixWord ++ tailWord_719925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719929 : List Nat := [1, 2, 1, 5, 2, 3, 1, 1, 3, 4]
def baseStart_719929 : Nat := 118140960795 + 719929 * 2 ^ 59
def prefixEnd_719929 : Nat := 4983230072969 + 3 ^ 40 * 719929 * 2
def baseEnd_719929 : Nat := 123223204703606336058871

theorem tailTrace_719929 : CollatzResearch.WordTrace tailWord_719929 prefixEnd_719929 123223204703606336058871 := by
  unfold tailWord_719929
  simp only [CollatzResearch.WordTrace]
  refine ⟨26257967808827661929434841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17505311872551774619623227 26257967808827661929434841)
  ·
    refine ⟨19693475856620746447076131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26257967808827661929434841 19693475856620746447076131)
    ·
      refine ⟨29540213784931119670614197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19693475856620746447076131 29540213784931119670614197)
      ·
        refine ⟨2769395042337292469120081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29540213784931119670614197 2769395042337292469120081)
        ·
          refine ⟨2077046281752969351840061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2769395042337292469120081 2077046281752969351840061)
          ·
            refine ⟨778892355657363506940023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2077046281752969351840061 778892355657363506940023)
            ·
              refine ⟨1168338533486045260410035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778892355657363506940023 1168338533486045260410035)
              ·
                refine ⟨1752507800229067890615053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168338533486045260410035 1752507800229067890615053)
                ·
                  refine ⟨657190425085900458980645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1752507800229067890615053 657190425085900458980645)
                  ·
                    refine ⟨123223204703606336058871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 657190425085900458980645 123223204703606336058871)
                    ·
                      rfl

theorem cell23_719929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 4].length) (baseStart_719929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719929 prefixEnd_719929 := by exact prefixLift 719929
  have htrace : WordTrace (prefixWord ++ tailWord_719929) baseStart_719929 baseEnd_719929 := by
    simpa [prefixWord, tailWord_719929, baseEnd_719929] using wordTrace_append hprefix tailTrace_719929
  have hstable : (prefixWord ++ tailWord_719929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719929).length < 2 ^ (prefixWord ++ tailWord_719929).sum := by decide
  have hdescent : baseEnd_719929 < baseStart_719929 := by decide
  rcases family_descends (prefixWord ++ tailWord_719929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719952 : List Nat := [2, 1, 1, 1, 1, 3, 1, 6, 3, 1, 3]
def baseStart_719952 : Nat := 118140960795 + 719952 * 2 ^ 59
def prefixEnd_719952 : Nat := 4983230072969 + 3 ^ 40 * 719952 * 2
def baseEnd_719952 : Nat := 369681424165872418189007

theorem tailTrace_719952 : CollatzResearch.WordTrace tailWord_719952 prefixEnd_719952 369681424165872418189007 := by
  unfold tailWord_719952
  simp only [CollatzResearch.WordTrace]
  refine ⟨13129403343872168428761055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17505871125162891238348073 13129403343872168428761055)
  ·
    refine ⟨19694105015808252643141583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13129403343872168428761055 19694105015808252643141583)
    ·
      refine ⟨29541157523712378964712375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19694105015808252643141583 29541157523712378964712375)
      ·
        refine ⟨44311736285568568447068563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29541157523712378964712375 44311736285568568447068563)
        ·
          refine ⟨66467604428352852670602845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44311736285568568447068563 66467604428352852670602845)
          ·
            refine ⟨24925351660632319751476067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66467604428352852670602845 24925351660632319751476067)
            ·
              refine ⟨37388027490948479627214101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24925351660632319751476067 37388027490948479627214101)
              ·
                refine ⟨1752563788638209982525661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37388027490948479627214101 1752563788638209982525661)
                ·
                  refine ⟨657211420739328743447123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1752563788638209982525661 657211420739328743447123)
                  ·
                    refine ⟨985817131108993115170685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 657211420739328743447123 985817131108993115170685)
                    ·
                      refine ⟨369681424165872418189007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 985817131108993115170685 369681424165872418189007)
                      ·
                        rfl

theorem cell23_719952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 3, 1, 3].length) (baseStart_719952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719952 prefixEnd_719952 := by exact prefixLift 719952
  have htrace : WordTrace (prefixWord ++ tailWord_719952) baseStart_719952 baseEnd_719952 := by
    simpa [prefixWord, tailWord_719952, baseEnd_719952] using wordTrace_append hprefix tailTrace_719952
  have hstable : (prefixWord ++ tailWord_719952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719952).length < 2 ^ (prefixWord ++ tailWord_719952).sum := by decide
  have hdescent : baseEnd_719952 < baseStart_719952 := by decide
  rcases family_descends (prefixWord ++ tailWord_719952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719986 : List Nat := [3, 2, 1, 2, 2, 1, 3, 4, 1, 1, 3]
def baseStart_719986 : Nat := 118140960795 + 719986 * 2 ^ 59
def prefixEnd_719986 : Nat := 4983230072969 + 3 ^ 40 * 719986 * 2
def baseEnd_719986 : Nat := 369698882508125285163851

theorem tailTrace_719986 : CollatzResearch.WordTrace tailWord_719986 prefixEnd_719986 369698882508125285163851 := by
  unfold tailWord_719986
  simp only [CollatzResearch.WordTrace]
  refine ⟨6565011692405290166064953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17506697846414107109506541 6565011692405290166064953)
  ·
    refine ⟨4923758769303967624548715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6565011692405290166064953 4923758769303967624548715)
    ·
      refine ⟨7385638153955951436823073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4923758769303967624548715 7385638153955951436823073)
      ·
        refine ⟨5539228615466963577617305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7385638153955951436823073 5539228615466963577617305)
        ·
          refine ⟨4154421461600222683212979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5539228615466963577617305 4154421461600222683212979)
          ·
            refine ⟨6231632192400334024819469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4154421461600222683212979 6231632192400334024819469)
            ·
              refine ⟨2336862072150125259307301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6231632192400334024819469 2336862072150125259307301)
              ·
                refine ⟨438161638528148486120119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2336862072150125259307301 438161638528148486120119)
                ·
                  refine ⟨657242457792222729180179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438161638528148486120119 657242457792222729180179)
                  ·
                    refine ⟨985863686688334093770269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 657242457792222729180179 985863686688334093770269)
                    ·
                      refine ⟨369698882508125285163851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 985863686688334093770269 369698882508125285163851)
                      ·
                        rfl

theorem cell23_719986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_719986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719986 prefixEnd_719986 := by exact prefixLift 719986
  have htrace : WordTrace (prefixWord ++ tailWord_719986) baseStart_719986 baseEnd_719986 := by
    simpa [prefixWord, tailWord_719986, baseEnd_719986] using wordTrace_append hprefix tailTrace_719986
  have hstable : (prefixWord ++ tailWord_719986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719986).length < 2 ^ (prefixWord ++ tailWord_719986).sum := by decide
  have hdescent : baseEnd_719986 < baseStart_719986 := by decide
  rcases family_descends (prefixWord ++ tailWord_719986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719995 : List Nat := [1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 5]
def baseStart_719995 : Nat := 118140960795 + 719995 * 2 ^ 59
def prefixEnd_719995 : Nat := 4983230072969 + 3 ^ 40 * 719995 * 2
def baseEnd_719995 : Nat := 369703503834015749951309

theorem tailTrace_719995 : CollatzResearch.WordTrace tailWord_719995 prefixEnd_719995 369703503834015749951309 := by
  unfold tailWord_719995
  simp only [CollatzResearch.WordTrace]
  refine ⟨26260375026588555201337439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17506916684392370134224959 26260375026588555201337439)
  ·
    refine ⟨39390562539882832802006159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26260375026588555201337439 39390562539882832802006159)
    ·
      refine ⟨59085843809824249203009239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39390562539882832802006159 59085843809824249203009239)
      ·
        refine ⟨88628765714736373804513859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59085843809824249203009239 88628765714736373804513859)
        ·
          refine ⟨132943148572104560706770789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88628765714736373804513859 132943148572104560706770789)
          ·
            refine ⟨24926840357269605132519523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132943148572104560706770789 24926840357269605132519523)
            ·
              refine ⟨37390260535904407698779285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24926840357269605132519523 37390260535904407698779285)
              ·
                refine ⟨1752668462620519110880279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37390260535904407698779285 1752668462620519110880279)
                ·
                  refine ⟨2629002693930778666320419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752668462620519110880279 2629002693930778666320419)
                  ·
                    refine ⟨3943504040896167999480629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2629002693930778666320419 3943504040896167999480629)
                    ·
                      refine ⟨369703503834015749951309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3943504040896167999480629 369703503834015749951309)
                      ·
                        rfl

theorem cell23_719995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 5].length) (baseStart_719995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_719995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_719995 prefixEnd_719995 := by exact prefixLift 719995
  have htrace : WordTrace (prefixWord ++ tailWord_719995) baseStart_719995 baseEnd_719995 := by
    simpa [prefixWord, tailWord_719995, baseEnd_719995] using wordTrace_append hprefix tailTrace_719995
  have hstable : (prefixWord ++ tailWord_719995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719995).length < 2 ^ (prefixWord ++ tailWord_719995).sum := by decide
  have hdescent : baseEnd_719995 < baseStart_719995 := by decide
  rcases family_descends (prefixWord ++ tailWord_719995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720009 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 5, 2, 2]
def baseStart_720009 : Nat := 118140960795 + 720009 * 2 ^ 59
def prefixEnd_720009 : Nat := 4983230072969 + 3 ^ 40 * 720009 * 2
def baseEnd_720009 : Nat := 369710692563178695176245

theorem tailTrace_720009 : CollatzResearch.WordTrace tailWord_720009 prefixEnd_720009 369710692563178695176245 := by
  unfold tailWord_720009
  simp only [CollatzResearch.WordTrace]
  refine ⟨26260885648537835592347081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17507257099025223728231387 26260885648537835592347081)
  ·
    refine ⟨19695664236403376694260311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26260885648537835592347081 19695664236403376694260311)
    ·
      refine ⟨29543496354605065041390467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19695664236403376694260311 29543496354605065041390467)
      ·
        refine ⟨44315244531907597562085701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29543496354605065041390467 44315244531907597562085701)
        ·
          refine ⟨8309108349732674542891069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44315244531907597562085701 8309108349732674542891069)
          ·
            refine ⟨3115915631149752953584151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8309108349732674542891069 3115915631149752953584151)
            ·
              refine ⟨4673873446724629430376227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3115915631149752953584151 4673873446724629430376227)
              ·
                refine ⟨7010810170086944145564341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4673873446724629430376227 7010810170086944145564341)
                ·
                  refine ⟨657263453445651013646657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7010810170086944145564341 657263453445651013646657)
                  ·
                    refine ⟨492947590084238260234993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 657263453445651013646657 492947590084238260234993)
                    ·
                      refine ⟨369710692563178695176245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 492947590084238260234993 369710692563178695176245)
                      ·
                        rfl

theorem cell23_720009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 2, 2].length) (baseStart_720009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720009 prefixEnd_720009 := by exact prefixLift 720009
  have htrace : WordTrace (prefixWord ++ tailWord_720009) baseStart_720009 baseEnd_720009 := by
    simpa [prefixWord, tailWord_720009, baseEnd_720009] using wordTrace_append hprefix tailTrace_720009
  have hstable : (prefixWord ++ tailWord_720009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720009).length < 2 ^ (prefixWord ++ tailWord_720009).sum := by decide
  have hdescent : baseEnd_720009 < baseStart_720009 := by decide
  rcases family_descends (prefixWord ++ tailWord_720009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720026 : List Nat := [3, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4]
def baseStart_720026 : Nat := 118140960795 + 720026 * 2 ^ 59
def prefixEnd_720026 : Nat := 4983230072969 + 3 ^ 40 * 720026 * 2
def baseEnd_720026 : Nat := 369719421734305128663667

theorem tailTrace_720026 : CollatzResearch.WordTrace tailWord_720026 prefixEnd_720026 369719421734305128663667 := by
  unfold tailWord_720026
  simp only [CollatzResearch.WordTrace]
  refine ⟨6565376422369061873928983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17507670459650831663810621 6565376422369061873928983)
  ·
    refine ⟨9848064633553592810893475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6565376422369061873928983 9848064633553592810893475)
    ·
      refine ⟨14772096950330389216340213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9848064633553592810893475 14772096950330389216340213)
      ·
        refine ⟨1384884089093473989031895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14772096950330389216340213 1384884089093473989031895)
        ·
          refine ⟨2077326133640210983547843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1384884089093473989031895 2077326133640210983547843)
          ·
            refine ⟨3115989200460316475321765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2077326133640210983547843 3115989200460316475321765)
            ·
              refine ⟨584247975086309339122831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3115989200460316475321765 584247975086309339122831)
              ·
                refine ⟨876371962629464008684247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 584247975086309339122831 876371962629464008684247)
                ·
                  refine ⟨1314557943944196013026371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876371962629464008684247 1314557943944196013026371)
                  ·
                    refine ⟨1971836915916294019539557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1314557943944196013026371 1971836915916294019539557)
                    ·
                      refine ⟨369719421734305128663667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1971836915916294019539557 369719421734305128663667)
                      ·
                        rfl

theorem cell23_720026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_720026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720026 prefixEnd_720026 := by exact prefixLift 720026
  have htrace : WordTrace (prefixWord ++ tailWord_720026) baseStart_720026 baseEnd_720026 := by
    simpa [prefixWord, tailWord_720026, baseEnd_720026] using wordTrace_append hprefix tailTrace_720026
  have hstable : (prefixWord ++ tailWord_720026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720026).length < 2 ^ (prefixWord ++ tailWord_720026).sum := by decide
  have hdescent : baseEnd_720026 < baseStart_720026 := by decide
  rcases family_descends (prefixWord ++ tailWord_720026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720029 : List Nat := [1, 4, 2, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_720029 : Nat := 118140960795 + 720029 * 2 ^ 59
def prefixEnd_720029 : Nat := 4983230072969 + 3 ^ 40 * 720029 * 2
def baseEnd_720029 : Nat := 369720962176268616926153

theorem tailTrace_720029 : CollatzResearch.WordTrace tailWord_720029 prefixEnd_720029 369720962176268616926153 := by
  unfold tailWord_720029
  simp only [CollatzResearch.WordTrace]
  refine ⟨26261615108465379008075141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17507743405643586005383427 26261615108465379008075141)
  ·
    refine ⟨4924052832837258564014089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26261615108465379008075141 4924052832837258564014089)
    ·
      refine ⟨3693039624627943923010567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4924052832837258564014089 3693039624627943923010567)
      ·
        refine ⟨5539559436941915884515851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3693039624627943923010567 5539559436941915884515851)
        ·
          refine ⟨8309339155412873826773777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5539559436941915884515851 8309339155412873826773777)
          ·
            refine ⟨6232004366559655370080333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8309339155412873826773777 6232004366559655370080333)
            ·
              refine ⟨2337001637459870763780125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6232004366559655370080333 2337001637459870763780125)
              ·
                refine ⟨876375614047451536417547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2337001637459870763780125 876375614047451536417547)
                ·
                  refine ⟨1314563421071177304626321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876375614047451536417547 1314563421071177304626321)
                  ·
                    refine ⟨985922565803382978469741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1314563421071177304626321 985922565803382978469741)
                    ·
                      refine ⟨369720962176268616926153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 985922565803382978469741 369720962176268616926153)
                      ·
                        rfl

theorem cell23_720029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_720029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720029 prefixEnd_720029 := by exact prefixLift 720029
  have htrace : WordTrace (prefixWord ++ tailWord_720029) baseStart_720029 baseEnd_720029 := by
    simpa [prefixWord, tailWord_720029, baseEnd_720029] using wordTrace_append hprefix tailTrace_720029
  have hstable : (prefixWord ++ tailWord_720029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720029).length < 2 ^ (prefixWord ++ tailWord_720029).sum := by decide
  have hdescent : baseEnd_720029 < baseStart_720029 := by decide
  rcases family_descends (prefixWord ++ tailWord_720029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720036 : List Nat := [2, 3, 1, 2, 3, 3, 1, 2, 2, 4]
def baseStart_720036 : Nat := 118140960795 + 720036 * 2 ^ 59
def prefixEnd_720036 : Nat := 4983230072969 + 3 ^ 40 * 720036 * 2
def baseEnd_720036 : Nat := 123241518846950029846207

theorem tailTrace_720036 : CollatzResearch.WordTrace tailWord_720036 prefixEnd_720036 123241518846950029846207 := by
  unfold tailWord_720036
  simp only [CollatzResearch.WordTrace]
  refine ⟨13130935209720009601789981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17507913612960012802386641 13130935209720009601789981)
  ·
    refine ⟨4924100703645003600671243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13130935209720009601789981 4924100703645003600671243)
    ·
      refine ⟨7386151055467505401006865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4924100703645003600671243 7386151055467505401006865)
      ·
        refine ⟨5539613291600629050755149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7386151055467505401006865 5539613291600629050755149)
        ·
          refine ⟨2077354984350235894033181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5539613291600629050755149 2077354984350235894033181)
          ·
            refine ⟨779008119131338460262443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2077354984350235894033181 779008119131338460262443)
            ·
              refine ⟨1168512178697007690393665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 779008119131338460262443 1168512178697007690393665)
              ·
                refine ⟨876384134022755767795249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1168512178697007690393665 876384134022755767795249)
                ·
                  refine ⟨657288100517066825846437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 876384134022755767795249 657288100517066825846437)
                  ·
                    refine ⟨123241518846950029846207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 657288100517066825846437 123241518846950029846207)
                    ·
                      rfl

theorem cell23_720036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_720036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720036 prefixEnd_720036 := by exact prefixLift 720036
  have htrace : WordTrace (prefixWord ++ tailWord_720036) baseStart_720036 baseEnd_720036 := by
    simpa [prefixWord, tailWord_720036, baseEnd_720036] using wordTrace_append hprefix tailTrace_720036
  have hstable : (prefixWord ++ tailWord_720036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720036).length < 2 ^ (prefixWord ++ tailWord_720036).sum := by decide
  have hdescent : baseEnd_720036 < baseStart_720036 := by decide
  rcases family_descends (prefixWord ++ tailWord_720036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720066 : List Nat := [3, 5, 1, 1, 2, 1, 1, 9]
def baseStart_720066 : Nat := 118140960795 + 720066 * 2 ^ 59
def prefixEnd_720066 : Nat := 4983230072969 + 3 ^ 40 * 720066 * 2
def baseEnd_720066 : Nat := 13694072628166110080129

theorem tailTrace_720066 : CollatzResearch.WordTrace tailWord_720066 prefixEnd_720066 13694072628166110080129 := by
  unfold tailWord_720066
  simp only [CollatzResearch.WordTrace]
  refine ⟨6565741152332833581793013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17508643072887556218114701 6565741152332833581793013)
  ·
    refine ⟨615538233031203148293095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6565741152332833581793013 615538233031203148293095)
    ·
      refine ⟨923307349546804722439643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 615538233031203148293095 923307349546804722439643)
      ·
        refine ⟨1384961024320207083659465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 923307349546804722439643 1384961024320207083659465)
        ·
          refine ⟨1038720768240155312744599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1384961024320207083659465 1038720768240155312744599)
          ·
            refine ⟨1558081152360232969116899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038720768240155312744599 1558081152360232969116899)
            ·
              refine ⟨2337121728540349453675349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1558081152360232969116899 2337121728540349453675349)
              ·
                refine ⟨13694072628166110080129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2337121728540349453675349 13694072628166110080129)
                ·
                  rfl

theorem cell23_720066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 9].length) (baseStart_720066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720066 prefixEnd_720066 := by exact prefixLift 720066
  have htrace : WordTrace (prefixWord ++ tailWord_720066) baseStart_720066 baseEnd_720066 := by
    simpa [prefixWord, tailWord_720066, baseEnd_720066] using wordTrace_append hprefix tailTrace_720066
  have hstable : (prefixWord ++ tailWord_720066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720066).length < 2 ^ (prefixWord ++ tailWord_720066).sum := by decide
  have hdescent : baseEnd_720066 < baseStart_720066 := by decide
  rcases family_descends (prefixWord ++ tailWord_720066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720075 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 4, 6]
def baseStart_720075 : Nat := 118140960795 + 720075 * 2 ^ 59
def prefixEnd_720075 : Nat := 4983230072969 + 3 ^ 40 * 720075 * 2
def baseEnd_720075 : Nat := 123248194095458478983647

theorem tailTrace_720075 : CollatzResearch.WordTrace tailWord_720075 prefixEnd_720075 123248194095458478983647 := by
  unfold tailWord_720075
  simp only [CollatzResearch.WordTrace]
  refine ⟨26263292866298728864249679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17508861910865819242833119 26263292866298728864249679)
  ·
    refine ⟨39394939299448093296374519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26263292866298728864249679 39394939299448093296374519)
    ·
      refine ⟨59092408949172139944561779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39394939299448093296374519 59092408949172139944561779)
      ·
        refine ⟨88638613423758209916842669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59092408949172139944561779 88638613423758209916842669)
        ·
          refine ⟨33239480033909328718816001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88638613423758209916842669 33239480033909328718816001)
          ·
            refine ⟨24929610025431996539112001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33239480033909328718816001 24929610025431996539112001)
            ·
              refine ⟨18697207519073997404334001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24929610025431996539112001 18697207519073997404334001)
              ·
                refine ⟨14022905639305498053250501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18697207519073997404334001 14022905639305498053250501)
                ·
                  refine ⟨2629294807369780884984469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14022905639305498053250501 2629294807369780884984469)
                  ·
                    refine ⟨123248194095458478983647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2629294807369780884984469 123248194095458478983647)
                    ·
                      rfl

theorem cell23_720075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 6].length) (baseStart_720075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720075 prefixEnd_720075 := by exact prefixLift 720075
  have htrace : WordTrace (prefixWord ++ tailWord_720075) baseStart_720075 baseEnd_720075 := by
    simpa [prefixWord, tailWord_720075, baseEnd_720075] using wordTrace_append hprefix tailTrace_720075
  have hstable : (prefixWord ++ tailWord_720075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720075).length < 2 ^ (prefixWord ++ tailWord_720075).sum := by decide
  have hdescent : baseEnd_720075 < baseStart_720075 := by decide
  rcases family_descends (prefixWord ++ tailWord_720075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720156 : List Nat := [2, 2, 3, 1, 1, 1, 6, 2, 5]
def baseStart_720156 : Nat := 118140960795 + 720156 * 2 ^ 59
def prefixEnd_720156 : Nat := 4983230072969 + 3 ^ 40 * 720156 * 2
def baseEnd_720156 : Nat := 41087352691043291115341

theorem tailTrace_720156 : CollatzResearch.WordTrace tailWord_720156 prefixEnd_720156 41087352691043291115341 := by
  unfold tailWord_720156
  simp only [CollatzResearch.WordTrace]
  refine ⟨13133123589502639848974161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17510831452670186465298881 13133123589502639848974161)
  ·
    refine ⟨9849842692126979886730621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13133123589502639848974161 9849842692126979886730621)
    ·
      refine ⟨3693691009547617457523983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9849842692126979886730621 3693691009547617457523983)
      ·
        refine ⟨5540536514321426186285975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3693691009547617457523983 5540536514321426186285975)
        ·
          refine ⟨8310804771482139279428963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5540536514321426186285975 8310804771482139279428963)
          ·
            refine ⟨12466207157223208919143445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8310804771482139279428963 12466207157223208919143445)
            ·
              refine ⟨584353460494837918084849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12466207157223208919143445 584353460494837918084849)
              ·
                refine ⟨438265095371128438563637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584353460494837918084849 438265095371128438563637)
                ·
                  refine ⟨41087352691043291115341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 438265095371128438563637 41087352691043291115341)
                  ·
                    rfl

theorem cell23_720156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 5].length) (baseStart_720156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720156 prefixEnd_720156 := by exact prefixLift 720156
  have htrace : WordTrace (prefixWord ++ tailWord_720156) baseStart_720156 baseEnd_720156 := by
    simpa [prefixWord, tailWord_720156, baseEnd_720156] using wordTrace_append hprefix tailTrace_720156
  have hstable : (prefixWord ++ tailWord_720156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720156).length < 2 ^ (prefixWord ++ tailWord_720156).sum := by decide
  have hdescent : baseEnd_720156 < baseStart_720156 := by decide
  rcases family_descends (prefixWord ++ tailWord_720156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720172 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 4]
def baseStart_720172 : Nat := 118140960795 + 720172 * 2 ^ 59
def prefixEnd_720172 : Nat := 4983230072969 + 3 ^ 40 * 720172 * 2
def baseEnd_720172 : Nat := 369794389909861557437995

theorem tailTrace_720172 : CollatzResearch.WordTrace tailWord_720172 prefixEnd_720172 369794389909861557437995 := by
  unfold tailWord_720172
  simp only [CollatzResearch.WordTrace]
  refine ⟨13133415373473657215265385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17511220497964876287020513 13133415373473657215265385)
  ·
    refine ⟨9850061530105242911449039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13133415373473657215265385 9850061530105242911449039)
    ·
      refine ⟨14775092295157864367173559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9850061530105242911449039 14775092295157864367173559)
      ·
        refine ⟨22162638442736796550760339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14775092295157864367173559 22162638442736796550760339)
        ·
          refine ⟨33243957664105194826140509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22162638442736796550760339 33243957664105194826140509)
          ·
            refine ⟨12466484124039448059802691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33243957664105194826140509 12466484124039448059802691)
            ·
              refine ⟨18699726186059172089704037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12466484124039448059802691 18699726186059172089704037)
              ·
                refine ⟨3506198659886094766819507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18699726186059172089704037 3506198659886094766819507)
                ·
                  refine ⟨5259297989829142150229261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3506198659886094766819507 5259297989829142150229261)
                  ·
                    refine ⟨1972236746185928306335973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5259297989829142150229261 1972236746185928306335973)
                    ·
                      refine ⟨369794389909861557437995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1972236746185928306335973 369794389909861557437995)
                      ·
                        rfl

theorem cell23_720172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_720172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720172 prefixEnd_720172 := by exact prefixLift 720172
  have htrace : WordTrace (prefixWord ++ tailWord_720172) baseStart_720172 baseEnd_720172 := by
    simpa [prefixWord, tailWord_720172, baseEnd_720172] using wordTrace_append hprefix tailTrace_720172
  have hstable : (prefixWord ++ tailWord_720172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720172).length < 2 ^ (prefixWord ++ tailWord_720172).sum := by decide
  have hdescent : baseEnd_720172 < baseStart_720172 := by decide
  rcases family_descends (prefixWord ++ tailWord_720172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720202 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_720202 : Nat := 118140960795 + 720202 * 2 ^ 59
def prefixEnd_720202 : Nat := 4983230072969 + 3 ^ 40 * 720202 * 2
def baseEnd_720202 : Nat := 369809794329496440062857

theorem tailTrace_720202 : CollatzResearch.WordTrace tailWord_720202 prefixEnd_720202 369809794329496440062857 := by
  unfold tailWord_720202
  simp only [CollatzResearch.WordTrace]
  refine ⟨6566981234209657388530715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17511949957892419702748573 6566981234209657388530715)
  ·
    refine ⟨9850471851314486082796073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6566981234209657388530715 9850471851314486082796073)
    ·
      refine ⟨7387853888485864562097055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9850471851314486082796073 7387853888485864562097055)
      ·
        refine ⟨11081780832728796843145583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7387853888485864562097055 11081780832728796843145583)
        ·
          refine ⟨16622671249093195264718375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11081780832728796843145583 16622671249093195264718375)
          ·
            refine ⟨24934006873639792897077563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16622671249093195264718375 24934006873639792897077563)
            ·
              refine ⟨37401010310459689345616345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24934006873639792897077563 37401010310459689345616345)
              ·
                refine ⟨28050757732844767009212259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37401010310459689345616345 28050757732844767009212259)
                ·
                  refine ⟨42076136599267150513818389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28050757732844767009212259 42076136599267150513818389)
                  ·
                    refine ⟨1972318903090647680335237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42076136599267150513818389 1972318903090647680335237)
                    ·
                      refine ⟨369809794329496440062857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1972318903090647680335237 369809794329496440062857)
                      ·
                        rfl

theorem cell23_720202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_720202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720202 prefixEnd_720202 := by exact prefixLift 720202
  have htrace : WordTrace (prefixWord ++ tailWord_720202) baseStart_720202 baseEnd_720202 := by
    simpa [prefixWord, tailWord_720202, baseEnd_720202] using wordTrace_append hprefix tailTrace_720202
  have hstable : (prefixWord ++ tailWord_720202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720202).length < 2 ^ (prefixWord ++ tailWord_720202).sum := by decide
  have hdescent : baseEnd_720202 < baseStart_720202 := by decide
  rcases family_descends (prefixWord ++ tailWord_720202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720209 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 4, 2, 3]
def baseStart_720209 : Nat := 118140960795 + 720209 * 2 ^ 59
def prefixEnd_720209 : Nat := 4983230072969 + 3 ^ 40 * 720209 * 2
def baseEnd_720209 : Nat := 369813388694077912675325

theorem tailTrace_720209 : CollatzResearch.WordTrace tailWord_720209 prefixEnd_720209 369813388694077912675325 := by
  unfold tailWord_720209
  simp only [CollatzResearch.WordTrace]
  refine ⟨26268180247813269749627681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17512120165208846499751787 26268180247813269749627681)
  ·
    refine ⟨19701135185859952312220761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26268180247813269749627681 19701135185859952312220761)
    ·
      refine ⟨14775851389394964234165571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19701135185859952312220761 14775851389394964234165571)
      ·
        refine ⟨22163777084092446351248357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14775851389394964234165571 22163777084092446351248357)
        ·
          refine ⟨4155708203267333690859067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22163777084092446351248357 4155708203267333690859067)
          ·
            refine ⟨6233562304901000536288601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4155708203267333690859067 6233562304901000536288601)
            ·
              refine ⟨4675171728675750402216451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6233562304901000536288601 4675171728675750402216451)
              ·
                refine ⟨7012757593013625603324677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4675171728675750402216451 7012757593013625603324677)
                ·
                  refine ⟨1314892048690054800623377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7012757593013625603324677 1314892048690054800623377)
                  ·
                    refine ⟨986169036517541100467533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1314892048690054800623377 986169036517541100467533)
                    ·
                      refine ⟨369813388694077912675325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 986169036517541100467533 369813388694077912675325)
                      ·
                        rfl

theorem cell23_720209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_720209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720209 prefixEnd_720209 := by exact prefixLift 720209
  have htrace : WordTrace (prefixWord ++ tailWord_720209) baseStart_720209 baseEnd_720209 := by
    simpa [prefixWord, tailWord_720209, baseEnd_720209] using wordTrace_append hprefix tailTrace_720209
  have hstable : (prefixWord ++ tailWord_720209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720209).length < 2 ^ (prefixWord ++ tailWord_720209).sum := by decide
  have hdescent : baseEnd_720209 < baseStart_720209 := by decide
  rcases family_descends (prefixWord ++ tailWord_720209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720216 : List Nat := [2, 1, 2, 2, 1, 1, 3, 6, 1, 4]
def baseStart_720216 : Nat := 118140960795 + 720216 * 2 ^ 59
def prefixEnd_720216 : Nat := 4983230072969 + 3 ^ 40 * 720216 * 2
def baseEnd_720216 : Nat := 123272327686219795095931

theorem tailTrace_720216 : CollatzResearch.WordTrace tailWord_720216 prefixEnd_720216 123272327686219795095931 := by
  unfold tailWord_720216
  simp only [CollatzResearch.WordTrace]
  refine ⟨13134217779393954972566251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17512290372525273296755001 13134217779393954972566251)
  ·
    refine ⟨19701326669090932458849377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13134217779393954972566251 19701326669090932458849377)
    ·
      refine ⟨14775995001818199344137033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19701326669090932458849377 14775995001818199344137033)
      ·
        refine ⟨11081996251363649508102775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14775995001818199344137033 11081996251363649508102775)
        ·
          refine ⟨16622994377045474262154163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11081996251363649508102775 16622994377045474262154163)
          ·
            refine ⟨24934491565568211393231245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16622994377045474262154163 24934491565568211393231245)
            ·
              refine ⟨9350434337088079272461717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24934491565568211393231245 9350434337088079272461717)
              ·
                refine ⟨438301609551003715896643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9350434337088079272461717 438301609551003715896643)
                ·
                  refine ⟨657452414326505573844965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438301609551003715896643 657452414326505573844965)
                  ·
                    refine ⟨123272327686219795095931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 657452414326505573844965 123272327686219795095931)
                    ·
                      rfl

theorem cell23_720216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 1, 4].length) (baseStart_720216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720216 prefixEnd_720216 := by exact prefixLift 720216
  have htrace : WordTrace (prefixWord ++ tailWord_720216) baseStart_720216 baseEnd_720216 := by
    simpa [prefixWord, tailWord_720216, baseEnd_720216] using wordTrace_append hprefix tailTrace_720216
  have hstable : (prefixWord ++ tailWord_720216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720216).length < 2 ^ (prefixWord ++ tailWord_720216).sum := by decide
  have hdescent : baseEnd_720216 < baseStart_720216 := by decide
  rcases family_descends (prefixWord ++ tailWord_720216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720279 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 4]
def baseStart_720279 : Nat := 118140960795 + 720279 * 2 ^ 59
def prefixEnd_720279 : Nat := 4983230072969 + 3 ^ 40 * 720279 * 2
def baseEnd_720279 : Nat := 369849332339892638800003

theorem tailTrace_720279 : CollatzResearch.WordTrace tailWord_720279 prefixEnd_720279 369849332339892638800003 := by
  unfold tailWord_720279
  simp only [CollatzResearch.WordTrace]
  refine ⟨26270733357559671704675891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17513822238373114469783927 26270733357559671704675891)
  ·
    refine ⟨39406100036339507557013837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26270733357559671704675891 39406100036339507557013837)
    ·
      refine ⟨14777287513627315333880189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39406100036339507557013837 14777287513627315333880189)
      ·
        refine ⟨5541482817610243250205071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14777287513627315333880189 5541482817610243250205071)
        ·
          refine ⟨8312224226415364875307607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5541482817610243250205071 8312224226415364875307607)
          ·
            refine ⟨12468336339623047312961411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8312224226415364875307607 12468336339623047312961411)
            ·
              refine ⟨18702504509434570969442117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12468336339623047312961411 18702504509434570969442117)
              ·
                refine ⟨3506719595518982056770397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18702504509434570969442117 3506719595518982056770397)
                ·
                  refine ⟨1315019848319618271288899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3506719595518982056770397 1315019848319618271288899)
                  ·
                    refine ⟨1972529772479427406933349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1315019848319618271288899 1972529772479427406933349)
                    ·
                      refine ⟨369849332339892638800003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1972529772479427406933349 369849332339892638800003)
                      ·
                        rfl

theorem cell23_720279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_720279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720279 prefixEnd_720279 := by exact prefixLift 720279
  have htrace : WordTrace (prefixWord ++ tailWord_720279) baseStart_720279 baseEnd_720279 := by
    simpa [prefixWord, tailWord_720279, baseEnd_720279] using wordTrace_append hprefix tailTrace_720279
  have hstable : (prefixWord ++ tailWord_720279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720279).length < 2 ^ (prefixWord ++ tailWord_720279).sum := by decide
  have hdescent : baseEnd_720279 < baseStart_720279 := by decide
  rcases family_descends (prefixWord ++ tailWord_720279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720280 : List Nat := [2, 1, 2, 5, 3, 1, 2, 1, 6]
def baseStart_720280 : Nat := 118140960795 + 720280 * 2 ^ 59
def prefixEnd_720280 : Nat := 4983230072969 + 3 ^ 40 * 720280 * 2
def baseEnd_720280 : Nat := 41094427313394126098611

theorem tailTrace_720280 : CollatzResearch.WordTrace tailWord_720280 prefixEnd_720280 41094427313394126098611 := by
  unfold tailWord_720280
  simp only [CollatzResearch.WordTrace]
  refine ⟨13135384915278024437731147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17513846553704032583641529 13135384915278024437731147)
  ·
    refine ⟨19703077372917036656596721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13135384915278024437731147 19703077372917036656596721)
    ·
      refine ⟨14777308029687777492447541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19703077372917036656596721 14777308029687777492447541)
      ·
        refine ⟨1385372627783229139916957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14777308029687777492447541 1385372627783229139916957)
        ·
          refine ⟨519514735418710927468859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1385372627783229139916957 519514735418710927468859)
          ·
            refine ⟨779272103128066391203289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519514735418710927468859 779272103128066391203289)
            ·
              refine ⟨584454077346049793402467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 779272103128066391203289 584454077346049793402467)
              ·
                refine ⟨876681116019074690103701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 584454077346049793402467 876681116019074690103701)
                ·
                  refine ⟨41094427313394126098611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 876681116019074690103701 41094427313394126098611)
                  ·
                    rfl

theorem cell23_720280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 6].length) (baseStart_720280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720280 prefixEnd_720280 := by exact prefixLift 720280
  have htrace : WordTrace (prefixWord ++ tailWord_720280) baseStart_720280 baseEnd_720280 := by
    simpa [prefixWord, tailWord_720280, baseEnd_720280] using wordTrace_append hprefix tailTrace_720280
  have hstable : (prefixWord ++ tailWord_720280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720280).length < 2 ^ (prefixWord ++ tailWord_720280).sum := by decide
  have hdescent : baseEnd_720280 < baseStart_720280 := by decide
  rcases family_descends (prefixWord ++ tailWord_720280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720324 : List Nat := [2, 3, 3, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_720324 : Nat := 118140960795 + 720324 * 2 ^ 59
def prefixEnd_720324 : Nat := 4983230072969 + 3 ^ 40 * 720324 * 2
def baseEnd_720324 : Nat := 369872438969344962737297

theorem tailTrace_720324 : CollatzResearch.WordTrace tailWord_720324 prefixEnd_720324 369872438969344962737297 := by
  unfold tailWord_720324
  simp only [CollatzResearch.WordTrace]
  refine ⟨13136187321198322195032013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17514916428264429593376017 13136187321198322195032013)
  ·
    refine ⟨4926070245449370823137005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13136187321198322195032013 4926070245449370823137005)
    ·
      refine ⟨1847276342043514058676377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4926070245449370823137005 1847276342043514058676377)
      ·
        refine ⟨1385457256532635544007283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1847276342043514058676377 1385457256532635544007283)
        ·
          refine ⟨2078185884798953316010925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1385457256532635544007283 2078185884798953316010925)
          ·
            refine ⟨779319706799607493504097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2078185884798953316010925 779319706799607493504097)
            ·
              refine ⟨584489780099705620128073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 779319706799607493504097 584489780099705620128073)
              ·
                refine ⟨438367335074779215096055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584489780099705620128073 438367335074779215096055)
                ·
                  refine ⟨657551002612168822644083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438367335074779215096055 657551002612168822644083)
                  ·
                    refine ⟨986326503918253233966125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 657551002612168822644083 986326503918253233966125)
                    ·
                      refine ⟨369872438969344962737297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 986326503918253233966125 369872438969344962737297)
                      ·
                        rfl

theorem cell23_720324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_720324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720324 prefixEnd_720324 := by exact prefixLift 720324
  have htrace : WordTrace (prefixWord ++ tailWord_720324) baseStart_720324 baseEnd_720324 := by
    simpa [prefixWord, tailWord_720324, baseEnd_720324] using wordTrace_append hprefix tailTrace_720324
  have hstable : (prefixWord ++ tailWord_720324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720324).length < 2 ^ (prefixWord ++ tailWord_720324).sum := by decide
  have hdescent : baseEnd_720324 < baseStart_720324 := by decide
  rcases family_descends (prefixWord ++ tailWord_720324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720329 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 5, 3, 3]
def baseStart_720329 : Nat := 118140960795 + 720329 * 2 ^ 59
def prefixEnd_720329 : Nat := 4983230072969 + 3 ^ 40 * 720329 * 2
def baseEnd_720329 : Nat := 369875006372617443174773

theorem tailTrace_720329 : CollatzResearch.WordTrace tailWord_720329 prefixEnd_720329 369875006372617443174773 := by
  unfold tailWord_720329
  simp only [CollatzResearch.WordTrace]
  refine ⟨26272557007378530243996041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17515038004919020162664027 26272557007378530243996041)
  ·
    refine ⟨19704417755533897682997031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26272557007378530243996041 19704417755533897682997031)
    ·
      refine ⟨29556626633300846524495547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19704417755533897682997031 29556626633300846524495547)
      ·
        refine ⟨44334939949951269786743321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29556626633300846524495547 44334939949951269786743321)
        ·
          refine ⟨33251204962463452340057491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44334939949951269786743321 33251204962463452340057491)
          ·
            refine ⟨49876807443695178510086237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33251204962463452340057491 49876807443695178510086237)
            ·
              refine ⟨18703802791385691941282339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49876807443695178510086237 18703802791385691941282339)
              ·
                refine ⟨28055704187078537911923509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18703802791385691941282339 28055704187078537911923509)
                ·
                  refine ⟨2630222267538612929242829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28055704187078537911923509 2630222267538612929242829)
                  ·
                    refine ⟨986333350326979848466061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2630222267538612929242829 986333350326979848466061)
                    ·
                      refine ⟨369875006372617443174773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 986333350326979848466061 369875006372617443174773)
                      ·
                        rfl

theorem cell23_720329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 3, 3].length) (baseStart_720329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720329 prefixEnd_720329 := by exact prefixLift 720329
  have htrace : WordTrace (prefixWord ++ tailWord_720329) baseStart_720329 baseEnd_720329 := by
    simpa [prefixWord, tailWord_720329, baseEnd_720329] using wordTrace_append hprefix tailTrace_720329
  have hstable : (prefixWord ++ tailWord_720329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720329).length < 2 ^ (prefixWord ++ tailWord_720329).sum := by decide
  have hdescent : baseEnd_720329 < baseStart_720329 := by decide
  rcases family_descends (prefixWord ++ tailWord_720329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720346 : List Nat := [3, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3]
def baseStart_720346 : Nat := 118140960795 + 720346 * 2 ^ 59
def prefixEnd_720346 : Nat := 4983230072969 + 3 ^ 40 * 720346 * 2
def baseEnd_720346 : Nat := 369883735543743876662195

theorem tailTrace_720346 : CollatzResearch.WordTrace tailWord_720346 prefixEnd_720346 369883735543743876662195 := by
  unfold tailWord_720346
  simp only [CollatzResearch.WordTrace]
  refine ⟨6568294262079235536841223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17515451365544628098243261 6568294262079235536841223)
  ·
    refine ⟨9852441393118853305261835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6568294262079235536841223 9852441393118853305261835)
    ·
      refine ⟨14778662089678279957892753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9852441393118853305261835 14778662089678279957892753)
      ·
        refine ⟨11083996567258709968419565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14778662089678279957892753 11083996567258709968419565)
        ·
          refine ⟨4156498712722016238157337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11083996567258709968419565 4156498712722016238157337)
          ·
            refine ⟨3117374034541512178618003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4156498712722016238157337 3117374034541512178618003)
            ·
              refine ⟨4676061051812268267927005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3117374034541512178618003 4676061051812268267927005)
              ·
                refine ⟨1753522894429600600472627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4676061051812268267927005 1753522894429600600472627)
                ·
                  refine ⟨2630284341644400900708941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753522894429600600472627 2630284341644400900708941)
                  ·
                    refine ⟨986356628116650337765853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2630284341644400900708941 986356628116650337765853)
                    ·
                      refine ⟨369883735543743876662195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 986356628116650337765853 369883735543743876662195)
                      ·
                        rfl

theorem cell23_720346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_720346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720346 prefixEnd_720346 := by exact prefixLift 720346
  have htrace : WordTrace (prefixWord ++ tailWord_720346) baseStart_720346 baseEnd_720346 := by
    simpa [prefixWord, tailWord_720346, baseEnd_720346] using wordTrace_append hprefix tailTrace_720346
  have hstable : (prefixWord ++ tailWord_720346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720346).length < 2 ^ (prefixWord ++ tailWord_720346).sum := by decide
  have hdescent : baseEnd_720346 < baseStart_720346 := by decide
  rcases family_descends (prefixWord ++ tailWord_720346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720389 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 4, 1, 5]
def baseStart_720389 : Nat := 118140960795 + 720389 * 2 ^ 59
def prefixEnd_720389 : Nat := 4983230072969 + 3 ^ 40 * 720389 * 2
def baseEnd_720389 : Nat := 369905815211887208424497

theorem tailTrace_720389 : CollatzResearch.WordTrace tailWord_720389 prefixEnd_720389 369905815211887208424497 := by
  unfold tailWord_720389
  simp only [CollatzResearch.WordTrace]
  refine ⟨26274745387161160491180221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17516496924774106994120147 26274745387161160491180221)
  ·
    refine ⟨9853029520185435184192583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26274745387161160491180221 9853029520185435184192583)
    ·
      refine ⟨14779544280278152776288875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9853029520185435184192583 14779544280278152776288875)
      ·
        refine ⟨22169316420417229164433313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14779544280278152776288875 22169316420417229164433313)
        ·
          refine ⟨16626987315312921873324985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22169316420417229164433313 16626987315312921873324985)
          ·
            refine ⟨12470240486484691404993739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16626987315312921873324985 12470240486484691404993739)
            ·
              refine ⟨18705360729727037107490609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12470240486484691404993739 18705360729727037107490609)
              ·
                refine ⟨14029020547295277830617957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18705360729727037107490609 14029020547295277830617957)
                ·
                  refine ⟨2630441352617864593240867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14029020547295277830617957 2630441352617864593240867)
                  ·
                    refine ⟨3945662028926796889861301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2630441352617864593240867 3945662028926796889861301)
                    ·
                      refine ⟨369905815211887208424497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3945662028926796889861301 369905815211887208424497)
                      ·
                        rfl

theorem cell23_720389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_720389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720389 prefixEnd_720389 := by exact prefixLift 720389
  have htrace : WordTrace (prefixWord ++ tailWord_720389) baseStart_720389 baseEnd_720389 := by
    simpa [prefixWord, tailWord_720389, baseEnd_720389] using wordTrace_append hprefix tailTrace_720389
  have hstable : (prefixWord ++ tailWord_720389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720389).length < 2 ^ (prefixWord ++ tailWord_720389).sum := by decide
  have hdescent : baseEnd_720389 < baseStart_720389 := by decide
  rcases family_descends (prefixWord ++ tailWord_720389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720399 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 4]
def baseStart_720399 : Nat := 118140960795 + 720399 * 2 ^ 59
def prefixEnd_720399 : Nat := 4983230072969 + 3 ^ 40 * 720399 * 2
def baseEnd_720399 : Nat := 369910950018432169299451

theorem tailTrace_720399 : CollatzResearch.WordTrace tailWord_720399 prefixEnd_720399 369910950018432169299451 := by
  unfold tailWord_720399
  simp only [CollatzResearch.WordTrace]
  refine ⟨26275110117124932199044251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17516740078083288132696167 26275110117124932199044251)
  ·
    refine ⟨39412665175687398298566377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26275110117124932199044251 39412665175687398298566377)
    ·
      refine ⟨29559498881765548723924783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39412665175687398298566377 29559498881765548723924783)
      ·
        refine ⟨44339248322648323085887175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29559498881765548723924783 44339248322648323085887175)
        ·
          refine ⟨66508872483972484628830763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44339248322648323085887175 66508872483972484628830763)
          ·
            refine ⟨99763308725958726943246145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66508872483972484628830763 99763308725958726943246145)
            ·
              refine ⟨74822481544469045207434609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99763308725958726943246145 74822481544469045207434609)
              ·
                refine ⟨56116861158351783905575957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74822481544469045207434609 56116861158351783905575957)
                ·
                  refine ⟨2630477866797739870573873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56116861158351783905575957 2630477866797739870573873)
                  ·
                    refine ⟨1972858400098304902930405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2630477866797739870573873 1972858400098304902930405)
                    ·
                      refine ⟨369910950018432169299451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1972858400098304902930405 369910950018432169299451)
                      ·
                        rfl

theorem cell23_720399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_720399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720399 prefixEnd_720399 := by exact prefixLift 720399
  have htrace : WordTrace (prefixWord ++ tailWord_720399) baseStart_720399 baseEnd_720399 := by
    simpa [prefixWord, tailWord_720399, baseEnd_720399] using wordTrace_append hprefix tailTrace_720399
  have hstable : (prefixWord ++ tailWord_720399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720399).length < 2 ^ (prefixWord ++ tailWord_720399).sum := by decide
  have hdescent : baseEnd_720399 < baseStart_720399 := by decide
  rcases family_descends (prefixWord ++ tailWord_720399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720403 : List Nat := [1, 1, 1, 2, 1, 6, 3, 1, 1, 4, 2]
def baseStart_720403 : Nat := 118140960795 + 720403 * 2 ^ 59
def prefixEnd_720403 : Nat := 4983230072969 + 3 ^ 40 * 720403 * 2
def baseEnd_720403 : Nat := 369913003941050153649433

theorem tailTrace_720403 : CollatzResearch.WordTrace tailWord_720403 prefixEnd_720403 369913003941050153649433 := by
  unfold tailWord_720403
  simp only [CollatzResearch.WordTrace]
  refine ⟨26275256009110440882189863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17516837339406960588126575 26275256009110440882189863)
  ·
    refine ⟨39412884013665661323284795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26275256009110440882189863 39412884013665661323284795)
    ·
      refine ⟨59119326020498491984927193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39412884013665661323284795 59119326020498491984927193)
      ·
        refine ⟨44339494515373868988695395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59119326020498491984927193 44339494515373868988695395)
        ·
          refine ⟨66509241773060803483043093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44339494515373868988695395 66509241773060803483043093)
          ·
            refine ⟨3117620708112225163267645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66509241773060803483043093 3117620708112225163267645)
            ·
              refine ⟨1169107765542084436225367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3117620708112225163267645 1169107765542084436225367)
              ·
                refine ⟨1753661648313126654338051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1169107765542084436225367 1753661648313126654338051)
                ·
                  refine ⟨2630492472469689981507077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753661648313126654338051 2630492472469689981507077)
                  ·
                    refine ⟨493217338588066871532577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2630492472469689981507077 493217338588066871532577)
                    ·
                      refine ⟨369913003941050153649433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 493217338588066871532577 369913003941050153649433)
                      ·
                        rfl

theorem cell23_720403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 4, 2].length) (baseStart_720403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720403 prefixEnd_720403 := by exact prefixLift 720403
  have htrace : WordTrace (prefixWord ++ tailWord_720403) baseStart_720403 baseEnd_720403 := by
    simpa [prefixWord, tailWord_720403, baseEnd_720403] using wordTrace_append hprefix tailTrace_720403
  have hstable : (prefixWord ++ tailWord_720403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720403).length < 2 ^ (prefixWord ++ tailWord_720403).sum := by decide
  have hdescent : baseEnd_720403 < baseStart_720403 := by decide
  rcases family_descends (prefixWord ++ tailWord_720403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720479 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 9]
def baseStart_720479 : Nat := 118140960795 + 720479 * 2 ^ 59
def prefixEnd_720479 : Nat := 4983230072969 + 3 ^ 40 * 720479 * 2
def baseEnd_720479 : Nat := 369952028470791856299083

theorem tailTrace_720479 : CollatzResearch.WordTrace tailWord_720479 prefixEnd_720479 369952028470791856299083 := by
  unfold tailWord_720479
  simp only [CollatzResearch.WordTrace]
  refine ⟨26278027956835105861956491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17518685304556737241304327 26278027956835105861956491)
  ·
    refine ⟨39417041935252658792934737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26278027956835105861956491 39417041935252658792934737)
    ·
      refine ⟨29562781451439494094701053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39417041935252658792934737 29562781451439494094701053)
      ·
        refine ⟨11086043044289810285512895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29562781451439494094701053 11086043044289810285512895)
        ·
          refine ⟨16629064566434715428269343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11086043044289810285512895 16629064566434715428269343)
          ·
            refine ⟨24943596849652073142404015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16629064566434715428269343 24943596849652073142404015)
            ·
              refine ⟨37415395274478109713606023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24943596849652073142404015 37415395274478109713606023)
              ·
                refine ⟨56123092911717164570409035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37415395274478109713606023 56123092911717164570409035)
                ·
                  refine ⟨84184639367575746855613553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56123092911717164570409035 84184639367575746855613553)
                  ·
                    refine ⟨63138479525681810141710165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84184639367575746855613553 63138479525681810141710165)
                    ·
                      refine ⟨369952028470791856299083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 63138479525681810141710165 369952028470791856299083)
                      ·
                        rfl

theorem cell23_720479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_720479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720479 prefixEnd_720479 := by exact prefixLift 720479
  have htrace : WordTrace (prefixWord ++ tailWord_720479) baseStart_720479 baseEnd_720479 := by
    simpa [prefixWord, tailWord_720479, baseEnd_720479] using wordTrace_append hprefix tailTrace_720479
  have hstable : (prefixWord ++ tailWord_720479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720479).length < 2 ^ (prefixWord ++ tailWord_720479).sum := by decide
  have hdescent : baseEnd_720479 < baseStart_720479 := by decide
  rcases family_descends (prefixWord ++ tailWord_720479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720494 : List Nat := [4, 1, 2, 2, 4, 1, 2, 2, 5]
def baseStart_720494 : Nat := 118140960795 + 720494 * 2 ^ 59
def prefixEnd_720494 : Nat := 4983230072969 + 3 ^ 40 * 720494 * 2
def baseEnd_720494 : Nat := 41106636742289921956835

theorem tailTrace_720494 : CollatzResearch.WordTrace tailWord_720494 prefixEnd_720494 41106636742289921956835 := by
  unfold tailWord_720494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3284821881472595427969067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17519050034520508949168357 3284821881472595427969067)
  ·
    refine ⟨4927232822208893141953601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3284821881472595427969067 4927232822208893141953601)
    ·
      refine ⟨3695424616656669856465201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4927232822208893141953601 3695424616656669856465201)
      ·
        refine ⟨2771568462492502392348901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3695424616656669856465201 2771568462492502392348901)
        ·
          refine ⟨519669086717344198565419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2771568462492502392348901 519669086717344198565419)
          ·
            refine ⟨779503630076016297848129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519669086717344198565419 779503630076016297848129)
            ·
              refine ⟨584627722557012223386097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 779503630076016297848129 584627722557012223386097)
              ·
                refine ⟨438470791917759167539573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584627722557012223386097 438470791917759167539573)
                ·
                  refine ⟨41106636742289921956835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 438470791917759167539573 41106636742289921956835)
                  ·
                    rfl

theorem cell23_720494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_720494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720494 prefixEnd_720494 := by exact prefixLift 720494
  have htrace : WordTrace (prefixWord ++ tailWord_720494) baseStart_720494 baseEnd_720494 := by
    simpa [prefixWord, tailWord_720494, baseEnd_720494] using wordTrace_append hprefix tailTrace_720494
  have hstable : (prefixWord ++ tailWord_720494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720494).length < 2 ^ (prefixWord ++ tailWord_720494).sum := by decide
  have hdescent : baseEnd_720494 < baseStart_720494 := by decide
  rcases family_descends (prefixWord ++ tailWord_720494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720499 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 12]
def baseStart_720499 : Nat := 118140960795 + 720499 * 2 ^ 59
def prefixEnd_720499 : Nat := 4983230072969 + 3 ^ 40 * 720499 * 2
def baseEnd_720499 : Nat := 41106922009320197560999

theorem tailTrace_720499 : CollatzResearch.WordTrace tailWord_720499 prefixEnd_720499 41106922009320197560999 := by
  unfold tailWord_720499
  simp only [CollatzResearch.WordTrace]
  refine ⟨26278757416762649277684551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17519171611175099518456367 26278757416762649277684551)
  ·
    refine ⟨39418136125143973916526827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26278757416762649277684551 39418136125143973916526827)
    ·
      refine ⟨59127204187715960874790241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39418136125143973916526827 59127204187715960874790241)
      ·
        refine ⟨44345403140786970656092681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59127204187715960874790241 44345403140786970656092681)
        ·
          refine ⟨33259052355590227992069511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44345403140786970656092681 33259052355590227992069511)
          ·
            refine ⟨49888578533385341988104267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33259052355590227992069511 49888578533385341988104267)
            ·
              refine ⟨74832867800078012982156401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49888578533385341988104267 74832867800078012982156401)
              ·
                refine ⟨56124650850058509736617301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74832867800078012982156401 56124650850058509736617301)
                ·
                  refine ⟨41106922009320197560999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 56124650850058509736617301 41106922009320197560999)
                  ·
                    rfl

theorem cell23_720499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 12].length) (baseStart_720499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720499 prefixEnd_720499 := by exact prefixLift 720499
  have htrace : WordTrace (prefixWord ++ tailWord_720499) baseStart_720499 baseEnd_720499 := by
    simpa [prefixWord, tailWord_720499, baseEnd_720499] using wordTrace_append hprefix tailTrace_720499
  have hstable : (prefixWord ++ tailWord_720499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720499).length < 2 ^ (prefixWord ++ tailWord_720499).sum := by decide
  have hdescent : baseEnd_720499 < baseStart_720499 := by decide
  rcases family_descends (prefixWord ++ tailWord_720499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720530 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_720530 : Nat := 118140960795 + 720530 * 2 ^ 59
def prefixEnd_720530 : Nat := 4983230072969 + 3 ^ 40 * 720530 * 2
def baseEnd_720530 : Nat := 369978215984171156761349

theorem tailTrace_720530 : CollatzResearch.WordTrace tailWord_720530 prefixEnd_720530 369978215984171156761349 := by
  unfold tailWord_720530
  simp only [CollatzResearch.WordTrace]
  refine ⟨6569972019912585393015761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17519925386433561048042029 6569972019912585393015761)
  ·
    refine ⟨4927479014934439044761821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6569972019912585393015761 4927479014934439044761821)
    ·
      refine ⟨1847804630600414641785683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4927479014934439044761821 1847804630600414641785683)
      ·
        refine ⟨2771706945900621962678525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1847804630600414641785683 2771706945900621962678525)
        ·
          refine ⟨1039390104712733236004447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2771706945900621962678525 1039390104712733236004447)
          ·
            refine ⟨1559085157069099854006671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039390104712733236004447 1559085157069099854006671)
            ·
              refine ⟨2338627735603649781010007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1559085157069099854006671 2338627735603649781010007)
              ·
                refine ⟨3507941603405474671515011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2338627735603649781010007 3507941603405474671515011)
                ·
                  refine ⟨5261912405108212007272517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507941603405474671515011 5261912405108212007272517)
                  ·
                    refine ⟨986608575957789751363597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5261912405108212007272517 986608575957789751363597)
                    ·
                      refine ⟨369978215984171156761349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 986608575957789751363597 369978215984171156761349)
                      ·
                        rfl

theorem cell23_720530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_720530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720530 prefixEnd_720530 := by exact prefixLift 720530
  have htrace : WordTrace (prefixWord ++ tailWord_720530) baseStart_720530 baseEnd_720530 := by
    simpa [prefixWord, tailWord_720530, baseEnd_720530] using wordTrace_append hprefix tailTrace_720530
  have hstable : (prefixWord ++ tailWord_720530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720530).length < 2 ^ (prefixWord ++ tailWord_720530).sum := by decide
  have hdescent : baseEnd_720530 < baseStart_720530 := by decide
  rcases family_descends (prefixWord ++ tailWord_720530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720580 : List Nat := [2, 3, 3, 1, 1, 1, 4, 2, 1, 5]
def baseStart_720580 : Nat := 118140960795 + 720580 * 2 ^ 59
def prefixEnd_720580 : Nat := 4983230072969 + 3 ^ 40 * 720580 * 2
def baseEnd_720580 : Nat := 123334630005631987045373

theorem tailTrace_720580 : CollatzResearch.WordTrace tailWord_720580 prefixEnd_720580 123334630005631987045373 := by
  unfold tailWord_720580
  simp only [CollatzResearch.WordTrace]
  refine ⟨13140855864734600055691597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17521141152979466740922129 13140855864734600055691597)
  ·
    refine ⟨4927820949275475020884349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13140855864734600055691597 4927820949275475020884349)
    ·
      refine ⟨1847932855978303132831631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4927820949275475020884349 1847932855978303132831631)
      ·
        refine ⟨2771899283967454699247447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1847932855978303132831631 2771899283967454699247447)
        ·
          refine ⟨4157848925951182048871171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2771899283967454699247447 4157848925951182048871171)
          ·
            refine ⟨6236773388926773073306757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4157848925951182048871171 6236773388926773073306757)
            ·
              refine ⟨1169395010423769951245017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6236773388926773073306757 1169395010423769951245017)
              ·
                refine ⟨877046257817827463433763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1169395010423769951245017 877046257817827463433763)
                ·
                  refine ⟨1315569386726741195150645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 877046257817827463433763 1315569386726741195150645)
                  ·
                    refine ⟨123334630005631987045373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1315569386726741195150645 123334630005631987045373)
                    ·
                      rfl

theorem cell23_720580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_720580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720580 prefixEnd_720580 := by exact prefixLift 720580
  have htrace : WordTrace (prefixWord ++ tailWord_720580) baseStart_720580 baseEnd_720580 := by
    simpa [prefixWord, tailWord_720580, baseEnd_720580] using wordTrace_append hprefix tailTrace_720580
  have hstable : (prefixWord ++ tailWord_720580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720580).length < 2 ^ (prefixWord ++ tailWord_720580).sum := by decide
  have hdescent : baseEnd_720580 < baseStart_720580 := by decide
  rcases family_descends (prefixWord ++ tailWord_720580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720583 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 2, 6, 2]
def baseStart_720583 : Nat := 118140960795 + 720583 * 2 ^ 59
def prefixEnd_720583 : Nat := 4983230072969 + 3 ^ 40 * 720583 * 2
def baseEnd_720583 : Nat := 370005430458859449398605

theorem tailTrace_720583 : CollatzResearch.WordTrace tailWord_720583 prefixEnd_720583 370005430458859449398605 := by
  unfold tailWord_720583
  simp only [CollatzResearch.WordTrace]
  refine ⟨26281821148458331623742403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17521214098972221082494935 26281821148458331623742403)
  ·
    refine ⟨39422731722687497435613605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26281821148458331623742403 39422731722687497435613605)
    ·
      refine ⟨7391762198003905769177551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39422731722687497435613605 7391762198003905769177551)
      ·
        refine ⟨11087643297005858653766327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7391762198003905769177551 11087643297005858653766327)
        ·
          refine ⟨16631464945508787980649491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11087643297005858653766327 16631464945508787980649491)
          ·
            refine ⟨24947197418263181970974237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16631464945508787980649491 24947197418263181970974237)
            ·
              refine ⟨9355199031848693239115339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24947197418263181970974237 9355199031848693239115339)
              ·
                refine ⟨14032798547773039858673009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9355199031848693239115339 14032798547773039858673009)
                ·
                  refine ⟨10524598910829779894004757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14032798547773039858673009 10524598910829779894004757)
                  ·
                    refine ⟨493340573945145932531473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10524598910829779894004757 493340573945145932531473)
                    ·
                      refine ⟨370005430458859449398605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 493340573945145932531473 370005430458859449398605)
                      ·
                        rfl

theorem cell23_720583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_720583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720583 prefixEnd_720583 := by exact prefixLift 720583
  have htrace : WordTrace (prefixWord ++ tailWord_720583) baseStart_720583 baseEnd_720583 := by
    simpa [prefixWord, tailWord_720583, baseEnd_720583] using wordTrace_append hprefix tailTrace_720583
  have hstable : (prefixWord ++ tailWord_720583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720583).length < 2 ^ (prefixWord ++ tailWord_720583).sum := by decide
  have hdescent : baseEnd_720583 < baseStart_720583 := by decide
  rcases family_descends (prefixWord ++ tailWord_720583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720593 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 4, 4]
def baseStart_720593 : Nat := 118140960795 + 720593 * 2 ^ 59
def prefixEnd_720593 : Nat := 4983230072969 + 3 ^ 40 * 720593 * 2
def baseEnd_720593 : Nat := 123336855088468136757853

theorem tailTrace_720593 : CollatzResearch.WordTrace tailWord_720593 prefixEnd_720593 123336855088468136757853 := by
  unfold tailWord_720593
  simp only [CollatzResearch.WordTrace]
  refine ⟨26282185878422103331606433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17521457252281402221070955 26282185878422103331606433)
  ·
    refine ⟨19711639408816577498704825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26282185878422103331606433 19711639408816577498704825)
    ·
      refine ⟨14783729556612433124028619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19711639408816577498704825 14783729556612433124028619)
      ·
        refine ⟨22175594334918649686042929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14783729556612433124028619 22175594334918649686042929)
        ·
          refine ⟨16631695751188987264532197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22175594334918649686042929 16631695751188987264532197)
          ·
            refine ⟨3118442953347935112099787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16631695751188987264532197 3118442953347935112099787)
            ·
              refine ⟨4677664430021902668149681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3118442953347935112099787 4677664430021902668149681)
              ·
                refine ⟨3508248322516427001112261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4677664430021902668149681 3508248322516427001112261)
                ·
                  refine ⟨657796560471830062708549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3508248322516427001112261 657796560471830062708549)
                  ·
                    refine ⟨123336855088468136757853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 657796560471830062708549 123336855088468136757853)
                    ·
                      rfl

theorem cell23_720593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_720593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720593 prefixEnd_720593 := by exact prefixLift 720593
  have htrace : WordTrace (prefixWord ++ tailWord_720593) baseStart_720593 baseEnd_720593 := by
    simpa [prefixWord, tailWord_720593, baseEnd_720593] using wordTrace_append hprefix tailTrace_720593
  have hstable : (prefixWord ++ tailWord_720593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720593).length < 2 ^ (prefixWord ++ tailWord_720593).sum := by decide
  have hdescent : baseEnd_720593 < baseStart_720593 := by decide
  rcases family_descends (prefixWord ++ tailWord_720593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720594 : List Nat := [3, 2, 2, 2, 2, 1, 3, 3, 1, 1, 3]
def baseStart_720594 : Nat := 118140960795 + 720594 * 2 ^ 59
def prefixEnd_720594 : Nat := 4983230072969 + 3 ^ 40 * 720594 * 2
def baseEnd_720594 : Nat := 370011078746058906361055

theorem tailTrace_720594 : CollatzResearch.WordTrace tailWord_720594 prefixEnd_720594 370011078746058906361055 := by
  unfold tailWord_720594
  simp only [CollatzResearch.WordTrace]
  refine ⟨6570555587854620125598209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17521481567612320334928557 6570555587854620125598209)
  ·
    refine ⟨4927916690890965094198657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6570555587854620125598209 4927916690890965094198657)
    ·
      refine ⟨3695937518168223820648993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4927916690890965094198657 3695937518168223820648993)
      ·
        refine ⟨2771953138626167865486745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3695937518168223820648993 2771953138626167865486745)
        ·
          refine ⟨2078964853969625899115059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2771953138626167865486745 2078964853969625899115059)
          ·
            refine ⟨3118447280954438848672589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2078964853969625899115059 3118447280954438848672589)
            ·
              refine ⟨1169417730357914568252221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3118447280954438848672589 1169417730357914568252221)
              ·
                refine ⟨438531648884217963094583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1169417730357914568252221 438531648884217963094583)
                ·
                  refine ⟨657797473326326944641875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438531648884217963094583 657797473326326944641875)
                  ·
                    refine ⟨986696209989490416962813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 657797473326326944641875 986696209989490416962813)
                    ·
                      refine ⟨370011078746058906361055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 986696209989490416962813 370011078746058906361055)
                      ·
                        rfl

theorem cell23_720594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_720594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720594 prefixEnd_720594 := by exact prefixLift 720594
  have htrace : WordTrace (prefixWord ++ tailWord_720594) baseStart_720594 baseEnd_720594 := by
    simpa [prefixWord, tailWord_720594, baseEnd_720594] using wordTrace_append hprefix tailTrace_720594
  have hstable : (prefixWord ++ tailWord_720594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720594).length < 2 ^ (prefixWord ++ tailWord_720594).sum := by decide
  have hdescent : baseEnd_720594 < baseStart_720594 := by decide
  rcases family_descends (prefixWord ++ tailWord_720594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720604 : List Nat := [2, 2, 5, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_720604 : Nat := 118140960795 + 720604 * 2 ^ 59
def prefixEnd_720604 : Nat := 4983230072969 + 3 ^ 40 * 720604 * 2
def baseEnd_720604 : Nat := 370016213552603867236009

theorem tailTrace_720604 : CollatzResearch.WordTrace tailWord_720604 prefixEnd_720604 370016213552603867236009 := by
  unfold tailWord_720604
  simp only [CollatzResearch.WordTrace]
  refine ⟨13141293540691126105128433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17521724720921501473504577 13141293540691126105128433)
  ·
    refine ⟨9855970155518344578846325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13141293540691126105128433 9855970155518344578846325)
    ·
      refine ⟨923997202079844804266843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9855970155518344578846325 923997202079844804266843)
      ·
        refine ⟨1385995803119767206400265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 923997202079844804266843 1385995803119767206400265)
        ·
          refine ⟨1039496852339825404800199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1385995803119767206400265 1039496852339825404800199)
          ·
            refine ⟨1559245278509738107200299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039496852339825404800199 1559245278509738107200299)
            ·
              refine ⟨2338867917764607160800449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1559245278509738107200299 2338867917764607160800449)
              ·
                refine ⟨1754150938323455370600337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2338867917764607160800449 1754150938323455370600337)
                ·
                  refine ⟨1315613203742591527950253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1754150938323455370600337 1315613203742591527950253)
                  ·
                    refine ⟨493354951403471822981345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1315613203742591527950253 493354951403471822981345)
                    ·
                      refine ⟨370016213552603867236009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 493354951403471822981345 370016213552603867236009)
                      ·
                        rfl

theorem cell23_720604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_720604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720604 prefixEnd_720604 := by exact prefixLift 720604
  have htrace : WordTrace (prefixWord ++ tailWord_720604) baseStart_720604 baseEnd_720604 := by
    simpa [prefixWord, tailWord_720604, baseEnd_720604] using wordTrace_append hprefix tailTrace_720604
  have hstable : (prefixWord ++ tailWord_720604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720604).length < 2 ^ (prefixWord ++ tailWord_720604).sum := by decide
  have hdescent : baseEnd_720604 < baseStart_720604 := by decide
  rcases family_descends (prefixWord ++ tailWord_720604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720611 : List Nat := [1, 1, 1, 7, 2, 1, 3, 2, 1, 1, 3]
def baseStart_720611 : Nat := 118140960795 + 720611 * 2 ^ 59
def prefixEnd_720611 : Nat := 4983230072969 + 3 ^ 40 * 720611 * 2
def baseEnd_720611 : Nat := 370019807917185339848477

theorem tailTrace_720611 : CollatzResearch.WordTrace tailWord_720611 prefixEnd_720611 370019807917185339848477 := by
  unfold tailWord_720611
  simp only [CollatzResearch.WordTrace]
  refine ⟨26282842392356892405761687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17521894928237928270507791 26282842392356892405761687)
  ·
    refine ⟨39424263588535338608642531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26282842392356892405761687 39424263588535338608642531)
    ·
      refine ⟨59136395382803007912963797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39424263588535338608642531 59136395382803007912963797)
      ·
        refine ⟨1386009266784445497960089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 59136395382803007912963797 1386009266784445497960089)
        ·
          refine ⟨1039506950088334123470067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1386009266784445497960089 1039506950088334123470067)
          ·
            refine ⟨1559260425132501185205101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039506950088334123470067 1559260425132501185205101)
            ·
              refine ⟨584722659424687944451913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1559260425132501185205101 584722659424687944451913)
              ·
                refine ⟨438541994568515958338935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584722659424687944451913 438541994568515958338935)
                ·
                  refine ⟨657812991852773937508403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438541994568515958338935 657812991852773937508403)
                  ·
                    refine ⟨986719487779160906262605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 657812991852773937508403 986719487779160906262605)
                    ·
                      refine ⟨370019807917185339848477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 986719487779160906262605 370019807917185339848477)
                      ·
                        rfl

theorem cell23_720611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_720611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720611 prefixEnd_720611 := by exact prefixLift 720611
  have htrace : WordTrace (prefixWord ++ tailWord_720611) baseStart_720611 baseEnd_720611 := by
    simpa [prefixWord, tailWord_720611, baseEnd_720611] using wordTrace_append hprefix tailTrace_720611
  have hstable : (prefixWord ++ tailWord_720611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720611).length < 2 ^ (prefixWord ++ tailWord_720611).sum := by decide
  have hdescent : baseEnd_720611 < baseStart_720611 := by decide
  rcases family_descends (prefixWord ++ tailWord_720611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720650 : List Nat := [3, 1, 2, 2, 1, 4, 1, 2, 1, 3, 3]
def baseStart_720650 : Nat := 118140960795 + 720650 * 2 ^ 59
def prefixEnd_720650 : Nat := 4983230072969 + 3 ^ 40 * 720650 * 2
def baseEnd_720650 : Nat := 370039833662710687260797

theorem tailTrace_720650 : CollatzResearch.WordTrace tailWord_720650 prefixEnd_720650 370039833662710687260797 := by
  unfold tailWord_720650
  simp only [CollatzResearch.WordTrace]
  refine ⟨6571066209803900516607851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17522843226143734710954269 6571066209803900516607851)
  ·
    refine ⟨9856599314705850774911777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6571066209803900516607851 9856599314705850774911777)
    ·
      refine ⟨7392449486029388081183833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9856599314705850774911777 7392449486029388081183833)
      ·
        refine ⟨5544337114522041060887875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7392449486029388081183833 5544337114522041060887875)
        ·
          refine ⟨8316505671783061591331813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5544337114522041060887875 8316505671783061591331813)
          ·
            refine ⟨1559344813459324048374715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8316505671783061591331813 1559344813459324048374715)
            ·
              refine ⟨2339017220188986072562073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1559344813459324048374715 2339017220188986072562073)
              ·
                refine ⟨1754262915141739554421555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2339017220188986072562073 1754262915141739554421555)
                ·
                  refine ⟨2631394372712609331632333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1754262915141739554421555 2631394372712609331632333)
                  ·
                    refine ⟨986772889767228499362125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2631394372712609331632333 986772889767228499362125)
                    ·
                      refine ⟨370039833662710687260797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 986772889767228499362125 370039833662710687260797)
                      ·
                        rfl

theorem cell23_720650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_720650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720650 prefixEnd_720650 := by exact prefixLift 720650
  have htrace : WordTrace (prefixWord ++ tailWord_720650) baseStart_720650 baseEnd_720650 := by
    simpa [prefixWord, tailWord_720650, baseEnd_720650] using wordTrace_append hprefix tailTrace_720650
  have hstable : (prefixWord ++ tailWord_720650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720650).length < 2 ^ (prefixWord ++ tailWord_720650).sum := by decide
  have hdescent : baseEnd_720650 < baseStart_720650 := by decide
  rcases family_descends (prefixWord ++ tailWord_720650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720673 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_720673 : Nat := 118140960795 + 720673 * 2 ^ 59
def prefixEnd_720673 : Nat := 4983230072969 + 3 ^ 40 * 720673 * 2
def baseEnd_720673 : Nat := 370051643717764097273191

theorem tailTrace_720673 : CollatzResearch.WordTrace tailWord_720673 prefixEnd_720673 370051643717764097273191 := by
  unfold tailWord_720673
  simp only [CollatzResearch.WordTrace]
  refine ⟨26285103718132276994518673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17523402478754851329679115 26285103718132276994518673)
  ·
    refine ⟨19713827788599207745889005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26285103718132276994518673 19713827788599207745889005)
    ·
      refine ⟨7392685420724702904708377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19713827788599207745889005 7392685420724702904708377)
      ·
        refine ⟨5544514065543527178531283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7392685420724702904708377 5544514065543527178531283)
        ·
          refine ⟨8316771098315290767796925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5544514065543527178531283 8316771098315290767796925)
          ·
            refine ⟨3118789161868234037923847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8316771098315290767796925 3118789161868234037923847)
            ·
              refine ⟨4678183742802351056885771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3118789161868234037923847 4678183742802351056885771)
              ·
                refine ⟨7017275614203526585328657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4678183742802351056885771 7017275614203526585328657)
                ·
                  refine ⟨5262956710652644938996493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7017275614203526585328657 5262956710652644938996493)
                  ·
                    refine ⟨1973608766494741852123685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5262956710652644938996493 1973608766494741852123685)
                    ·
                      refine ⟨370051643717764097273191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1973608766494741852123685 370051643717764097273191)
                      ·
                        rfl

theorem cell23_720673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_720673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720673 prefixEnd_720673 := by exact prefixLift 720673
  have htrace : WordTrace (prefixWord ++ tailWord_720673) baseStart_720673 baseEnd_720673 := by
    simpa [prefixWord, tailWord_720673, baseEnd_720673] using wordTrace_append hprefix tailTrace_720673
  have hstable : (prefixWord ++ tailWord_720673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720673).length < 2 ^ (prefixWord ++ tailWord_720673).sum := by decide
  have hdescent : baseEnd_720673 < baseStart_720673 := by decide
  rcases family_descends (prefixWord ++ tailWord_720673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720694 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_720694 : Nat := 118140960795 + 720694 * 2 ^ 59
def prefixEnd_720694 : Nat := 4983230072969 + 3 ^ 40 * 720694 * 2
def baseEnd_720694 : Nat := 370062426811508515110595

theorem tailTrace_720694 : CollatzResearch.WordTrace tailWord_720694 prefixEnd_720694 370062426811508515110595 := by
  unfold tailWord_720694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1642866853191012348814571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17523913100704131720688757 1642866853191012348814571)
  ·
    refine ⟨2464300279786518523221857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1642866853191012348814571 2464300279786518523221857)
    ·
      refine ⟨1848225209839888892416393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2464300279786518523221857 1848225209839888892416393)
      ·
        refine ⟨1386168907379916669312295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1848225209839888892416393 1386168907379916669312295)
        ·
          refine ⟨2079253361069875003968443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1386168907379916669312295 2079253361069875003968443)
          ·
            refine ⟨3118880041604812505952665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2079253361069875003968443 3118880041604812505952665)
            ·
              refine ⟨2339160031203609379464499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3118880041604812505952665 2339160031203609379464499)
              ·
                refine ⟨3508740046805414069196749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2339160031203609379464499 3508740046805414069196749)
                ·
                  refine ⟨1315777517552030275948781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3508740046805414069196749 1315777517552030275948781)
                  ·
                    refine ⟨493416569082011353480793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1315777517552030275948781 493416569082011353480793)
                    ·
                      refine ⟨370062426811508515110595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 493416569082011353480793 370062426811508515110595)
                      ·
                        rfl

theorem cell23_720694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_720694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720694 prefixEnd_720694 := by exact prefixLift 720694
  have htrace : WordTrace (prefixWord ++ tailWord_720694) baseStart_720694 baseEnd_720694 := by
    simpa [prefixWord, tailWord_720694, baseEnd_720694] using wordTrace_append hprefix tailTrace_720694
  have hstable : (prefixWord ++ tailWord_720694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720694).length < 2 ^ (prefixWord ++ tailWord_720694).sum := by decide
  have hdescent : baseEnd_720694 < baseStart_720694 := by decide
  rcases family_descends (prefixWord ++ tailWord_720694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720724 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 4, 2, 2]
def baseStart_720724 : Nat := 118140960795 + 720724 * 2 ^ 59
def prefixEnd_720724 : Nat := 4983230072969 + 3 ^ 40 * 720724 * 2
def baseEnd_720724 : Nat := 370077831231143397735457

theorem tailTrace_720724 : CollatzResearch.WordTrace tailWord_720724 prefixEnd_720724 370077831231143397735457 := by
  unfold tailWord_720724
  simp only [CollatzResearch.WordTrace]
  refine ⟨13143481920473756352312613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17524642560631675136416817 13143481920473756352312613)
  ·
    refine ⟨2464402860088829316058615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13143481920473756352312613 2464402860088829316058615)
    ·
      refine ⟨3696604290133243974087923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2464402860088829316058615 3696604290133243974087923)
      ·
        refine ⟨5544906435199865961131885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3696604290133243974087923 5544906435199865961131885)
        ·
          refine ⟨2079339913199949735424457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5544906435199865961131885 2079339913199949735424457)
          ·
            refine ⟨1559504934899962301568343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2079339913199949735424457 1559504934899962301568343)
            ·
              refine ⟨2339257402349943452352515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1559504934899962301568343 2339257402349943452352515)
              ·
                refine ⟨3508886103524915178528773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2339257402349943452352515 3508886103524915178528773)
                ·
                  refine ⟨657916144410921595974145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3508886103524915178528773 657916144410921595974145)
                  ·
                    refine ⟨493437108308191196980609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 657916144410921595974145 493437108308191196980609)
                    ·
                      refine ⟨370077831231143397735457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 493437108308191196980609 370077831231143397735457)
                      ·
                        rfl

theorem cell23_720724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_720724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720724 prefixEnd_720724 := by exact prefixLift 720724
  have htrace : WordTrace (prefixWord ++ tailWord_720724) baseStart_720724 baseEnd_720724 := by
    simpa [prefixWord, tailWord_720724, baseEnd_720724] using wordTrace_append hprefix tailTrace_720724
  have hstable : (prefixWord ++ tailWord_720724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720724).length < 2 ^ (prefixWord ++ tailWord_720724).sum := by decide
  have hdescent : baseEnd_720724 < baseStart_720724 := by decide
  rcases family_descends (prefixWord ++ tailWord_720724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720730 : List Nat := [3, 1, 1, 2, 1, 3, 1, 6, 5]
def baseStart_720730 : Nat := 118140960795 + 720730 * 2 ^ 59
def prefixEnd_720730 : Nat := 4983230072969 + 3 ^ 40 * 720730 * 2
def baseEnd_720730 : Nat := 41120101346118930473381

theorem tailTrace_720730 : CollatzResearch.WordTrace tailWord_720730 prefixEnd_720730 41120101346118930473381 := by
  unfold tailWord_720730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6571795669731443932335911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17524788452617183819562429 6571795669731443932335911)
  ·
    refine ⟨9857693504597165898503867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6571795669731443932335911 9857693504597165898503867)
    ·
      refine ⟨14786540256895748847755801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9857693504597165898503867 14786540256895748847755801)
      ·
        refine ⟨11089905192671811635816851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14786540256895748847755801 11089905192671811635816851)
        ·
          refine ⟨16634857789007717453725277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11089905192671811635816851 16634857789007717453725277)
          ·
            refine ⟨6238071670877894045146979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16634857789007717453725277 6238071670877894045146979)
            ·
              refine ⟨9357107506316841067720469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6238071670877894045146979 9357107506316841067720469)
              ·
                refine ⟨438614414358601925049397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9357107506316841067720469 438614414358601925049397)
                ·
                  refine ⟨41120101346118930473381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 438614414358601925049397 41120101346118930473381)
                  ·
                    rfl

theorem cell23_720730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 5].length) (baseStart_720730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720730 prefixEnd_720730 := by exact prefixLift 720730
  have htrace : WordTrace (prefixWord ++ tailWord_720730) baseStart_720730 baseEnd_720730 := by
    simpa [prefixWord, tailWord_720730, baseEnd_720730] using wordTrace_append hprefix tailTrace_720730
  have hstable : (prefixWord ++ tailWord_720730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720730).length < 2 ^ (prefixWord ++ tailWord_720730).sum := by decide
  have hdescent : baseEnd_720730 < baseStart_720730 := by decide
  rcases family_descends (prefixWord ++ tailWord_720730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720743 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 3, 7]
def baseStart_720743 : Nat := 118140960795 + 720743 * 2 ^ 59
def prefixEnd_720743 : Nat := 4983230072969 + 3 ^ 40 * 720743 * 2
def baseEnd_720743 : Nat := 123362529121192941132623

theorem tailTrace_720743 : CollatzResearch.WordTrace tailWord_720743 prefixEnd_720743 123362529121192941132623 := by
  unfold tailWord_720743
  simp only [CollatzResearch.WordTrace]
  refine ⟨26287656827878678949566883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17525104551919119299711255 26287656827878678949566883)
  ·
    refine ⟨39431485241818018424350325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26287656827878678949566883 39431485241818018424350325)
    ·
      refine ⟨3696701741420439227282843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39431485241818018424350325 3696701741420439227282843)
      ·
        refine ⟨5545052612130658840924265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3696701741420439227282843 5545052612130658840924265)
        ·
          refine ⟨4158789459097994130693199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5545052612130658840924265 4158789459097994130693199)
          ·
            refine ⟨6238184188646991196039799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4158789459097994130693199 6238184188646991196039799)
            ·
              refine ⟨9357276282970486794059699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6238184188646991196039799 9357276282970486794059699)
              ·
                refine ⟨14035914424455730191089549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9357276282970486794059699 14035914424455730191089549)
                ·
                  refine ⟨5263467909170898821658581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14035914424455730191089549 5263467909170898821658581)
                  ·
                    refine ⟨123362529121192941132623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5263467909170898821658581 123362529121192941132623)
                    ·
                      rfl

theorem cell23_720743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_720743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720743 prefixEnd_720743 := by exact prefixLift 720743
  have htrace : WordTrace (prefixWord ++ tailWord_720743) baseStart_720743 baseEnd_720743 := by
    simpa [prefixWord, tailWord_720743, baseEnd_720743] using wordTrace_append hprefix tailTrace_720743
  have hstable : (prefixWord ++ tailWord_720743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720743).length < 2 ^ (prefixWord ++ tailWord_720743).sum := by decide
  have hdescent : baseEnd_720743 < baseStart_720743 := by decide
  rcases family_descends (prefixWord ++ tailWord_720743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720793 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 2, 1, 6]
def baseStart_720793 : Nat := 118140960795 + 720793 * 2 ^ 59
def prefixEnd_720793 : Nat := 4983230072969 + 3 ^ 40 * 720793 * 2
def baseEnd_720793 : Nat := 370113261396303627772639

theorem tailTrace_720793 : CollatzResearch.WordTrace tailWord_720793 prefixEnd_720793 370113261396303627772639 := by
  unfold tailWord_720793
  simp only [CollatzResearch.WordTrace]
  refine ⟨26289480477697537488887033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17526320318465024992591355 26289480477697537488887033)
  ·
    refine ⟨19717110358273153116665275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26289480477697537488887033 19717110358273153116665275)
    ·
      refine ⟨29575665537409729674997913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19717110358273153116665275 29575665537409729674997913)
      ·
        refine ⟨22181749153057297256248435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29575665537409729674997913 22181749153057297256248435)
        ·
          refine ⟨33272623729585945884372653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22181749153057297256248435 33272623729585945884372653)
          ·
            refine ⟨12477233898594729706639745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33272623729585945884372653 12477233898594729706639745)
            ·
              refine ⟨9357925423946047279979809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12477233898594729706639745 9357925423946047279979809)
              ·
                refine ⟨7018444067959535459984857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9357925423946047279979809 7018444067959535459984857)
                ·
                  refine ⟨5263833050969651594988643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7018444067959535459984857 5263833050969651594988643)
                  ·
                    refine ⟨7895749576454477392482965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5263833050969651594988643 7895749576454477392482965)
                    ·
                      refine ⟨370113261396303627772639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7895749576454477392482965 370113261396303627772639)
                      ·
                        rfl

theorem cell23_720793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_720793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720793 prefixEnd_720793 := by exact prefixLift 720793
  have htrace : WordTrace (prefixWord ++ tailWord_720793) baseStart_720793 baseEnd_720793 := by
    simpa [prefixWord, tailWord_720793, baseEnd_720793] using wordTrace_append hprefix tailTrace_720793
  have hstable : (prefixWord ++ tailWord_720793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720793).length < 2 ^ (prefixWord ++ tailWord_720793).sum := by decide
  have hdescent : baseEnd_720793 < baseStart_720793 := by decide
  rcases family_descends (prefixWord ++ tailWord_720793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720800 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 3]
def baseStart_720800 : Nat := 118140960795 + 720800 * 2 ^ 59
def prefixEnd_720800 : Nat := 4983230072969 + 3 ^ 40 * 720800 * 2
def baseEnd_720800 : Nat := 370116855760885100385107

theorem tailTrace_720800 : CollatzResearch.WordTrace tailWord_720800 prefixEnd_720800 370116855760885100385107 := by
  unfold tailWord_720800
  simp only [CollatzResearch.WordTrace]
  refine ⟨13144867894336088842195927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17526490525781451789594569 13144867894336088842195927)
  ·
    refine ⟨19717301841504133263293891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13144867894336088842195927 19717301841504133263293891)
    ·
      refine ⟨29575952762256199894940837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19717301841504133263293891 29575952762256199894940837)
      ·
        refine ⟨5545491142923037480301407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29575952762256199894940837 5545491142923037480301407)
        ·
          refine ⟨8318236714384556220452111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5545491142923037480301407 8318236714384556220452111)
          ·
            refine ⟨12477355071576834330678167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8318236714384556220452111 12477355071576834330678167)
            ·
              refine ⟨18716032607365251496017251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12477355071576834330678167 18716032607365251496017251)
              ·
                refine ⟨28074048911047877244025877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18716032607365251496017251 28074048911047877244025877)
                ·
                  refine ⟨1315971042705369245813713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28074048911047877244025877 1315971042705369245813713)
                  ·
                    refine ⟨986978282029026934360285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1315971042705369245813713 986978282029026934360285)
                    ·
                      refine ⟨370116855760885100385107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 986978282029026934360285 370116855760885100385107)
                      ·
                        rfl

theorem cell23_720800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_720800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720800 prefixEnd_720800 := by exact prefixLift 720800
  have htrace : WordTrace (prefixWord ++ tailWord_720800) baseStart_720800 baseEnd_720800 := by
    simpa [prefixWord, tailWord_720800, baseEnd_720800] using wordTrace_append hprefix tailTrace_720800
  have hstable : (prefixWord ++ tailWord_720800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720800).length < 2 ^ (prefixWord ++ tailWord_720800).sum := by decide
  have hdescent : baseEnd_720800 < baseStart_720800 := by decide
  rcases family_descends (prefixWord ++ tailWord_720800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720817 : List Nat := [1, 2, 2, 4, 2, 1, 1, 3, 2, 2, 3]
def baseStart_720817 : Nat := 118140960795 + 720817 * 2 ^ 59
def prefixEnd_720817 : Nat := 4983230072969 + 3 ^ 40 * 720817 * 2
def baseEnd_720817 : Nat := 370125584932011533872529

theorem tailTrace_720817 : CollatzResearch.WordTrace tailWord_720817 prefixEnd_720817 370125584932011533872529 := by
  unfold tailWord_720817
  simp only [CollatzResearch.WordTrace]
  refine ⟨26290355829610589587760705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17526903886407059725173803 26290355829610589587760705)
  ·
    refine ⟨19717766872207942190820529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26290355829610589587760705 19717766872207942190820529)
    ·
      refine ⟨14788325154155956643115397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19717766872207942190820529 14788325154155956643115397)
      ·
        refine ⟨2772810966404241870584137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14788325154155956643115397 2772810966404241870584137)
        ·
          refine ⟨2079608224803181402938103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2772810966404241870584137 2079608224803181402938103)
          ·
            refine ⟨3119412337204772104407155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2079608224803181402938103 3119412337204772104407155)
            ·
              refine ⟨4679118505807158156610733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3119412337204772104407155 4679118505807158156610733)
              ·
                refine ⟨1754669439677684308729025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4679118505807158156610733 1754669439677684308729025)
                ·
                  refine ⟨1316002079758263231546769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1754669439677684308729025 1316002079758263231546769)
                  ·
                    refine ⟨987001559818697423660077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1316002079758263231546769 987001559818697423660077)
                    ·
                      refine ⟨370125584932011533872529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 987001559818697423660077 370125584932011533872529)
                      ·
                        rfl

theorem cell23_720817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_720817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720817 prefixEnd_720817 := by exact prefixLift 720817
  have htrace : WordTrace (prefixWord ++ tailWord_720817) baseStart_720817 baseEnd_720817 := by
    simpa [prefixWord, tailWord_720817, baseEnd_720817] using wordTrace_append hprefix tailTrace_720817
  have hstable : (prefixWord ++ tailWord_720817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720817).length < 2 ^ (prefixWord ++ tailWord_720817).sum := by decide
  have hdescent : baseEnd_720817 < baseStart_720817 := by decide
  rcases family_descends (prefixWord ++ tailWord_720817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720823 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 8]
def baseStart_720823 : Nat := 118140960795 + 720823 * 2 ^ 59
def prefixEnd_720823 : Nat := 4983230072969 + 3 ^ 40 * 720823 * 2
def baseEnd_720823 : Nat := 370128665815938510397501

theorem tailTrace_720823 : CollatzResearch.WordTrace tailWord_720823 prefixEnd_720823 370128665815938510397501 := by
  unfold tailWord_720823
  simp only [CollatzResearch.WordTrace]
  refine ⟨26290574667588852612479123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17527049778392568408319415 26290574667588852612479123)
  ·
    refine ⟨39435862001383278918718685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26290574667588852612479123 39435862001383278918718685)
    ·
      refine ⟨14788448250518729594519507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39435862001383278918718685 14788448250518729594519507)
      ·
        refine ⟨22182672375778094391779261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14788448250518729594519507 22182672375778094391779261)
        ·
          refine ⟨8318502140916785396917223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22182672375778094391779261 8318502140916785396917223)
          ·
            refine ⟨12477753211375178095375835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8318502140916785396917223 12477753211375178095375835)
            ·
              refine ⟨18716629817062767143063753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12477753211375178095375835 18716629817062767143063753)
              ·
                refine ⟨14037472362797075357297815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18716629817062767143063753 14037472362797075357297815)
                ·
                  refine ⟨21056208544195613035946723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14037472362797075357297815 21056208544195613035946723)
                  ·
                    refine ⟨31584312816293419553920085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21056208544195613035946723 31584312816293419553920085)
                    ·
                      refine ⟨370128665815938510397501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 31584312816293419553920085 370128665815938510397501)
                      ·
                        rfl

theorem cell23_720823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_720823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720823 prefixEnd_720823 := by exact prefixLift 720823
  have htrace : WordTrace (prefixWord ++ tailWord_720823) baseStart_720823 baseEnd_720823 := by
    simpa [prefixWord, tailWord_720823, baseEnd_720823] using wordTrace_append hprefix tailTrace_720823
  have hstable : (prefixWord ++ tailWord_720823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720823).length < 2 ^ (prefixWord ++ tailWord_720823).sum := by decide
  have hdescent : baseEnd_720823 < baseStart_720823 := by decide
  rcases family_descends (prefixWord ++ tailWord_720823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720847 : List Nat := [1, 1, 2, 1, 1, 5, 2, 3, 3, 1, 3]
def baseStart_720847 : Nat := 118140960795 + 720847 * 2 ^ 59
def prefixEnd_720847 : Nat := 4983230072969 + 3 ^ 40 * 720847 * 2
def baseEnd_720847 : Nat := 370140989351646416497391

theorem tailTrace_720847 : CollatzResearch.WordTrace tailWord_720847 prefixEnd_720847 370140989351646416497391 := by
  unfold tailWord_720847
  simp only [CollatzResearch.WordTrace]
  refine ⟨26291450019501904711352795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17527633346334603140901863 26291450019501904711352795)
  ·
    refine ⟨39437175029252857067029193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26291450019501904711352795 39437175029252857067029193)
    ·
      refine ⟨29577881271939642800271895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39437175029252857067029193 29577881271939642800271895)
      ·
        refine ⟨44366821907909464200407843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29577881271939642800271895 44366821907909464200407843)
        ·
          refine ⟨66550232861864196300611765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44366821907909464200407843 66550232861864196300611765)
          ·
            refine ⟨6239084330799768403182353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66550232861864196300611765 6239084330799768403182353)
            ·
              refine ⟨4679313248099826302386765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6239084330799768403182353 4679313248099826302386765)
              ·
                refine ⟨1754742468037434863395037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4679313248099826302386765 1754742468037434863395037)
                ·
                  refine ⟨658028425514038073773139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1754742468037434863395037 658028425514038073773139)
                  ·
                    refine ⟨987042638271057110659709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 658028425514038073773139 987042638271057110659709)
                    ·
                      refine ⟨370140989351646416497391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 987042638271057110659709 370140989351646416497391)
                      ·
                        rfl

theorem cell23_720847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 1, 3].length) (baseStart_720847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720847 prefixEnd_720847 := by exact prefixLift 720847
  have htrace : WordTrace (prefixWord ++ tailWord_720847) baseStart_720847 baseEnd_720847 := by
    simpa [prefixWord, tailWord_720847, baseEnd_720847] using wordTrace_append hprefix tailTrace_720847
  have hstable : (prefixWord ++ tailWord_720847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720847).length < 2 ^ (prefixWord ++ tailWord_720847).sum := by decide
  have hdescent : baseEnd_720847 < baseStart_720847 := by decide
  rcases family_descends (prefixWord ++ tailWord_720847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720880 : List Nat := [2, 1, 1, 1, 3, 2, 4, 2, 1, 6]
def baseStart_720880 : Nat := 118140960795 + 720880 * 2 ^ 59
def prefixEnd_720880 : Nat := 4983230072969 + 3 ^ 40 * 720880 * 2
def baseEnd_720880 : Nat := 123385978071081595794913

theorem tailTrace_720880 : CollatzResearch.WordTrace tailWord_720880 prefixEnd_720880 123385978071081595794913 := by
  unfold tailWord_720880
  simp only [CollatzResearch.WordTrace]
  refine ⟨13146326814191175673652047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17528435752254900898202729 13146326814191175673652047)
  ·
    refine ⟨19719490221286763510478071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13146326814191175673652047 19719490221286763510478071)
    ·
      refine ⟨29579235331930145265717107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19719490221286763510478071 29579235331930145265717107)
      ·
        refine ⟨44368852997895217898575661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29579235331930145265717107 44368852997895217898575661)
        ·
          refine ⟨16638319874210706711965873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44368852997895217898575661 16638319874210706711965873)
          ·
            refine ⟨12478739905658030033974405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16638319874210706711965873 12478739905658030033974405)
            ·
              refine ⟨2339763732310880631370201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12478739905658030033974405 2339763732310880631370201)
              ·
                refine ⟨1754822799233160473527651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2339763732310880631370201 1754822799233160473527651)
                ·
                  refine ⟨2632234198849740710291477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1754822799233160473527651 2632234198849740710291477)
                  ·
                    refine ⟨123385978071081595794913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2632234198849740710291477 123385978071081595794913)
                    ·
                      rfl

theorem cell23_720880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 1, 6].length) (baseStart_720880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720880 prefixEnd_720880 := by exact prefixLift 720880
  have htrace : WordTrace (prefixWord ++ tailWord_720880) baseStart_720880 baseEnd_720880 := by
    simpa [prefixWord, tailWord_720880, baseEnd_720880] using wordTrace_append hprefix tailTrace_720880
  have hstable : (prefixWord ++ tailWord_720880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720880).length < 2 ^ (prefixWord ++ tailWord_720880).sum := by decide
  have hdescent : baseEnd_720880 < baseStart_720880 := by decide
  rcases family_descends (prefixWord ++ tailWord_720880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720897 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 4, 4]
def baseStart_720897 : Nat := 118140960795 + 720897 * 2 ^ 59
def prefixEnd_720897 : Nat := 4983230072969 + 3 ^ 40 * 720897 * 2
def baseEnd_720897 : Nat := 123388887794790406957387

theorem tailTrace_720897 : CollatzResearch.WordTrace tailWord_720897 prefixEnd_720897 123388887794790406957387 := by
  unfold tailWord_720897
  simp only [CollatzResearch.WordTrace]
  refine ⟨26293273669320763250672945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17528849112880508833781963 26293273669320763250672945)
  ·
    refine ⟨19719955251990572438004709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26293273669320763250672945 19719955251990572438004709)
    ·
      refine ⟨3697491609748232332125883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19719955251990572438004709 3697491609748232332125883)
      ·
        refine ⟨5546237414622348498188825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3697491609748232332125883 5546237414622348498188825)
        ·
          refine ⟨4159678060966761373641619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5546237414622348498188825 4159678060966761373641619)
          ·
            refine ⟨6239517091450142060462429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4159678060966761373641619 6239517091450142060462429)
            ·
              refine ⟨2339818909293803272673411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6239517091450142060462429 2339818909293803272673411)
              ·
                refine ⟨3509728363940704909010117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2339818909293803272673411 3509728363940704909010117)
                ·
                  refine ⟨658074068238882170439397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3509728363940704909010117 658074068238882170439397)
                  ·
                    refine ⟨123388887794790406957387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 658074068238882170439397 123388887794790406957387)
                    ·
                      rfl

theorem cell23_720897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_720897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720897 prefixEnd_720897 := by exact prefixLift 720897
  have htrace : WordTrace (prefixWord ++ tailWord_720897) baseStart_720897 baseEnd_720897 := by
    simpa [prefixWord, tailWord_720897, baseEnd_720897] using wordTrace_append hprefix tailTrace_720897
  have hstable : (prefixWord ++ tailWord_720897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720897).length < 2 ^ (prefixWord ++ tailWord_720897).sum := by decide
  have hdescent : baseEnd_720897 < baseStart_720897 := by decide
  rcases family_descends (prefixWord ++ tailWord_720897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720910 : List Nat := [4, 1, 1, 2, 2, 1, 2, 10]
def baseStart_720910 : Nat := 118140960795 + 720910 * 2 ^ 59
def prefixEnd_720910 : Nat := 4983230072969 + 3 ^ 40 * 720910 * 2
def baseEnd_720910 : Nat := 13710123653069617407763

theorem tailTrace_720910 : CollatzResearch.WordTrace tailWord_720910 prefixEnd_720910 13710123653069617407763 := by
  unfold tailWord_720910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3286718477284208308862023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17529165212182444313930789 3286718477284208308862023)
  ·
    refine ⟨4930077715926312463293035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3286718477284208308862023 4930077715926312463293035)
    ·
      refine ⟨7395116573889468694939553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4930077715926312463293035 7395116573889468694939553)
      ·
        refine ⟨5546337430417101521204665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7395116573889468694939553 5546337430417101521204665)
        ·
          refine ⟨4159753072812826140903499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5546337430417101521204665 4159753072812826140903499)
          ·
            refine ⟨6239629609219239211355249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4159753072812826140903499 6239629609219239211355249)
            ·
              refine ⟨4679722206914429408516437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6239629609219239211355249 4679722206914429408516437)
              ·
                refine ⟨13710123653069617407763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4679722206914429408516437 13710123653069617407763)
                ·
                  rfl

theorem cell23_720910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 10].length) (baseStart_720910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720910 prefixEnd_720910 := by exact prefixLift 720910
  have htrace : WordTrace (prefixWord ++ tailWord_720910) baseStart_720910 baseEnd_720910 := by
    simpa [prefixWord, tailWord_720910, baseEnd_720910] using wordTrace_append hprefix tailTrace_720910
  have hstable : (prefixWord ++ tailWord_720910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720910).length < 2 ^ (prefixWord ++ tailWord_720910).sum := by decide
  have hdescent : baseEnd_720910 < baseStart_720910 := by decide
  rcases family_descends (prefixWord ++ tailWord_720910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720917 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 1, 1, 6]
def baseStart_720917 : Nat := 118140960795 + 720917 * 2 ^ 59
def prefixEnd_720917 : Nat := 4983230072969 + 3 ^ 40 * 720917 * 2
def baseEnd_720917 : Nat := 370176932997461142622069

theorem tailTrace_720917 : CollatzResearch.WordTrace tailWord_720917 prefixEnd_720917 370176932997461142622069 := by
  unfold tailWord_720917
  simp only [CollatzResearch.WordTrace]
  refine ⟨26294003129248306666401005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17529335419498871110934003 26294003129248306666401005)
  ·
    refine ⟨9860251173468114999900377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26294003129248306666401005 9860251173468114999900377)
    ·
      refine ⟨7395188380101086249925283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9860251173468114999900377 7395188380101086249925283)
      ·
        refine ⟨11092782570151629374887925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7395188380101086249925283 11092782570151629374887925)
        ·
          refine ⟨1039948365951715253895743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11092782570151629374887925 1039948365951715253895743)
          ·
            refine ⟨1559922548927572880843615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039948365951715253895743 1559922548927572880843615)
            ·
              refine ⟨2339883823391359321265423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1559922548927572880843615 2339883823391359321265423)
              ·
                refine ⟨3509825735087038981898135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2339883823391359321265423 3509825735087038981898135)
                ·
                  refine ⟨5264738602630558472847203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3509825735087038981898135 5264738602630558472847203)
                  ·
                    refine ⟨7897107903945837709270805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5264738602630558472847203 7897107903945837709270805)
                    ·
                      refine ⟨370176932997461142622069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7897107903945837709270805 370176932997461142622069)
                      ·
                        rfl

theorem cell23_720917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_720917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720917 prefixEnd_720917 := by exact prefixLift 720917
  have htrace : WordTrace (prefixWord ++ tailWord_720917) baseStart_720917 baseEnd_720917 := by
    simpa [prefixWord, tailWord_720917, baseEnd_720917] using wordTrace_append hprefix tailTrace_720917
  have hstable : (prefixWord ++ tailWord_720917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720917).length < 2 ^ (prefixWord ++ tailWord_720917).sum := by decide
  have hdescent : baseEnd_720917 < baseStart_720917 := by decide
  rcases family_descends (prefixWord ++ tailWord_720917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720924 : List Nat := [2, 2, 3, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_720924 : Nat := 118140960795 + 720924 * 2 ^ 59
def prefixEnd_720924 : Nat := 4983230072969 + 3 ^ 40 * 720924 * 2
def baseEnd_720924 : Nat := 370180527362042615234537

theorem tailTrace_720924 : CollatzResearch.WordTrace tailWord_720924 prefixEnd_720924 370180527362042615234537 := by
  unfold tailWord_720924
  simp only [CollatzResearch.WordTrace]
  refine ⟨13147129220111473430952913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17529505626815297907937217 13147129220111473430952913)
  ·
    refine ⟨9860346915083605073214685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13147129220111473430952913 9860346915083605073214685)
    ·
      refine ⟨3697630093156351902455507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9860346915083605073214685 3697630093156351902455507)
      ·
        refine ⟨5546445139734527853683261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3697630093156351902455507 5546445139734527853683261)
        ·
          refine ⟨2079916927400447945131223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5546445139734527853683261 2079916927400447945131223)
          ·
            refine ⟨3119875391100671917696835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2079916927400447945131223 3119875391100671917696835)
            ·
              refine ⟨4679813086651007876545253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3119875391100671917696835 4679813086651007876545253)
              ·
                refine ⟨877464953747063976852235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4679813086651007876545253 877464953747063976852235)
                ·
                  refine ⟨1316197430620595965278353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 877464953747063976852235 1316197430620595965278353)
                  ·
                    refine ⟨987148072965446973958765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1316197430620595965278353 987148072965446973958765)
                    ·
                      refine ⟨370180527362042615234537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 987148072965446973958765 370180527362042615234537)
                      ·
                        rfl

theorem cell23_720924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_720924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720924 prefixEnd_720924 := by exact prefixLift 720924
  have htrace : WordTrace (prefixWord ++ tailWord_720924) baseStart_720924 baseEnd_720924 := by
    simpa [prefixWord, tailWord_720924, baseEnd_720924] using wordTrace_append hprefix tailTrace_720924
  have hstable : (prefixWord ++ tailWord_720924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720924).length < 2 ^ (prefixWord ++ tailWord_720924).sum := by decide
  have hdescent : baseEnd_720924 < baseStart_720924 := by decide
  rcases family_descends (prefixWord ++ tailWord_720924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720954 : List Nat := [3, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3]
def baseStart_720954 : Nat := 118140960795 + 720954 * 2 ^ 59
def prefixEnd_720954 : Nat := 4983230072969 + 3 ^ 40 * 720954 * 2
def baseEnd_720954 : Nat := 370195931781677497859399

theorem tailTrace_720954 : CollatzResearch.WordTrace tailWord_720954 prefixEnd_720954 370195931781677497859399 := by
  unfold tailWord_720954
  simp only [CollatzResearch.WordTrace]
  refine ⟨6573838157528565496374479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17530235086742841323665277 6573838157528565496374479)
  ·
    refine ⟨9860757236292848244561719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6573838157528565496374479 9860757236292848244561719)
    ·
      refine ⟨14791135854439272366842579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9860757236292848244561719 14791135854439272366842579)
      ·
        refine ⟨22186703781658908550263869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14791135854439272366842579 22186703781658908550263869)
        ·
          refine ⟨8320013918122090706348951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22186703781658908550263869 8320013918122090706348951)
          ·
            refine ⟨12480020877183136059523427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8320013918122090706348951 12480020877183136059523427)
            ·
              refine ⟨18720031315774704089285141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12480020877183136059523427 18720031315774704089285141)
              ·
                refine ⟨877501467926939254185241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18720031315774704089285141 877501467926939254185241)
                ·
                  refine ⟨658126100945204440638931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 877501467926939254185241 658126100945204440638931)
                  ·
                    refine ⟨987189151417806660958397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 658126100945204440638931 987189151417806660958397)
                    ·
                      refine ⟨370195931781677497859399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 987189151417806660958397 370195931781677497859399)
                      ·
                        rfl

theorem cell23_720954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3].length) (baseStart_720954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720954 prefixEnd_720954 := by exact prefixLift 720954
  have htrace : WordTrace (prefixWord ++ tailWord_720954) baseStart_720954 baseEnd_720954 := by
    simpa [prefixWord, tailWord_720954, baseEnd_720954] using wordTrace_append hprefix tailTrace_720954
  have hstable : (prefixWord ++ tailWord_720954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720954).length < 2 ^ (prefixWord ++ tailWord_720954).sum := by decide
  have hdescent : baseEnd_720954 < baseStart_720954 := by decide
  rcases family_descends (prefixWord ++ tailWord_720954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720970 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 1, 8]
def baseStart_720970 : Nat := 118140960795 + 720970 * 2 ^ 59
def prefixEnd_720970 : Nat := 4983230072969 + 3 ^ 40 * 720970 * 2
def baseEnd_720970 : Nat := 123401382490716478419775

theorem tailTrace_720970 : CollatzResearch.WordTrace tailWord_720970 prefixEnd_720970 123401382490716478419775 := by
  unfold tailWord_720970
  simp only [CollatzResearch.WordTrace]
  refine ⟨6573984049514074179520091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17530624132037531145386909 6573984049514074179520091)
  ·
    refine ⟨9860976074271111269280137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6573984049514074179520091 9860976074271111269280137)
    ·
      refine ⟨7395732055703333451960103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9860976074271111269280137 7395732055703333451960103)
      ·
        refine ⟨11093598083555000177940155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7395732055703333451960103 11093598083555000177940155)
        ·
          refine ⟨16640397125332500266910233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11093598083555000177940155 16640397125332500266910233)
          ·
            refine ⟨12480297843999375200182675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16640397125332500266910233 12480297843999375200182675)
            ·
              refine ⟨18720446765999062800274013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12480297843999375200182675 18720446765999062800274013)
              ·
                refine ⟨7020167537249648550102755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18720446765999062800274013 7020167537249648550102755)
                ·
                  refine ⟨10530251305874472825154133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7020167537249648550102755 10530251305874472825154133)
                  ·
                    refine ⟨123401382490716478419775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10530251305874472825154133 123401382490716478419775)
                    ·
                      rfl

theorem cell23_720970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_720970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720970 prefixEnd_720970 := by exact prefixLift 720970
  have htrace : WordTrace (prefixWord ++ tailWord_720970) baseStart_720970 baseEnd_720970 := by
    simpa [prefixWord, tailWord_720970, baseEnd_720970] using wordTrace_append hprefix tailTrace_720970
  have hstable : (prefixWord ++ tailWord_720970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720970).length < 2 ^ (prefixWord ++ tailWord_720970).sum := by decide
  have hdescent : baseEnd_720970 < baseStart_720970 := by decide
  rcases family_descends (prefixWord ++ tailWord_720970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720981 : List Nat := [1, 3, 2, 2, 1, 3, 3, 2, 1, 3, 2]
def baseStart_720981 : Nat := 118140960795 + 720981 * 2 ^ 59
def prefixEnd_720981 : Nat := 4983230072969 + 3 ^ 40 * 720981 * 2
def baseEnd_720981 : Nat := 370209795759348892221775

theorem tailTrace_720981 : CollatzResearch.WordTrace tailWord_720981 prefixEnd_720981 370209795759348892221775 := by
  unfold tailWord_720981
  simp only [CollatzResearch.WordTrace]
  refine ⟨26296337401016445596730797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17530891600677630397820531 26296337401016445596730797)
  ·
    refine ⟨9861126525381167098774049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26296337401016445596730797 9861126525381167098774049)
    ·
      refine ⟨7395844894035875324080537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9861126525381167098774049 7395844894035875324080537)
      ·
        refine ⟨5546883670526906493060403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7395844894035875324080537 5546883670526906493060403)
        ·
          refine ⟨8320325505790359739590605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5546883670526906493060403 8320325505790359739590605)
          ·
            refine ⟨3120122064671384902346477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8320325505790359739590605 3120122064671384902346477)
            ·
              refine ⟨1170045774251769338379929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3120122064671384902346477 1170045774251769338379929)
              ·
                refine ⟨877534330688827003784947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1170045774251769338379929 877534330688827003784947)
                ·
                  refine ⟨1316301496033240505677421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 877534330688827003784947 1316301496033240505677421)
                  ·
                    refine ⟨493613061012465189629033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1316301496033240505677421 493613061012465189629033)
                    ·
                      refine ⟨370209795759348892221775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 493613061012465189629033 370209795759348892221775)
                      ·
                        rfl

theorem cell23_720981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_720981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720981 prefixEnd_720981 := by exact prefixLift 720981
  have htrace : WordTrace (prefixWord ++ tailWord_720981) baseStart_720981 baseEnd_720981 := by
    simpa [prefixWord, tailWord_720981, baseEnd_720981] using wordTrace_append hprefix tailTrace_720981
  have hstable : (prefixWord ++ tailWord_720981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720981).length < 2 ^ (prefixWord ++ tailWord_720981).sum := by decide
  have hdescent : baseEnd_720981 < baseStart_720981 := by decide
  rcases family_descends (prefixWord ++ tailWord_720981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720997 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 2, 1, 5]
def baseStart_720997 : Nat := 118140960795 + 720997 * 2 ^ 59
def prefixEnd_720997 : Nat := 4983230072969 + 3 ^ 40 * 720997 * 2
def baseEnd_720997 : Nat := 370218011449820829621701

theorem tailTrace_720997 : CollatzResearch.WordTrace tailWord_720997 prefixEnd_720997 370218011449820829621701 := by
  unfold tailWord_720997
  simp only [CollatzResearch.WordTrace]
  refine ⟨26296920968958480329313245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17531280645972320219542163 26296920968958480329313245)
  ·
    refine ⟨9861345363359430123492467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26296920968958480329313245 9861345363359430123492467)
    ·
      refine ⟨14792018045039145185238701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9861345363359430123492467 14792018045039145185238701)
      ·
        refine ⟨5547006766889679444464513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14792018045039145185238701 5547006766889679444464513)
        ·
          refine ⟨4160255075167259583348385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5547006766889679444464513 4160255075167259583348385)
          ·
            refine ⟨3120191306375444687511289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4160255075167259583348385 3120191306375444687511289)
            ·
              refine ⟨2340143479781583515633467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3120191306375444687511289 2340143479781583515633467)
              ·
                refine ⟨3510215219672375273450201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2340143479781583515633467 3510215219672375273450201)
                ·
                  refine ⟨2632661414754281455087651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3510215219672375273450201 2632661414754281455087651)
                  ·
                    refine ⟨3948992122131422182631477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2632661414754281455087651 3948992122131422182631477)
                    ·
                      refine ⟨370218011449820829621701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3948992122131422182631477 370218011449820829621701)
                      ·
                        rfl

theorem cell23_720997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_720997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_720997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_720997 prefixEnd_720997 := by exact prefixLift 720997
  have htrace : WordTrace (prefixWord ++ tailWord_720997) baseStart_720997 baseEnd_720997 := by
    simpa [prefixWord, tailWord_720997, baseEnd_720997] using wordTrace_append hprefix tailTrace_720997
  have hstable : (prefixWord ++ tailWord_720997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720997).length < 2 ^ (prefixWord ++ tailWord_720997).sum := by decide
  have hdescent : baseEnd_720997 < baseStart_720997 := by decide
  rcases family_descends (prefixWord ++ tailWord_720997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721014 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_721014 : Nat := 118140960795 + 721014 * 2 ^ 59
def prefixEnd_721014 : Nat := 4983230072969 + 3 ^ 40 * 721014 * 2
def baseEnd_721014 : Nat := 370226740620947263109123

theorem tailTrace_721014 : CollatzResearch.WordTrace tailWord_721014 prefixEnd_721014 370226740620947263109123 := by
  unfold tailWord_721014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1643596313118555764542631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17531694006597928155121397 1643596313118555764542631)
  ·
    refine ⟨2465394469677833646813947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1643596313118555764542631 2465394469677833646813947)
    ·
      refine ⟨3698091704516750470220921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2465394469677833646813947 3698091704516750470220921)
      ·
        refine ⟨2773568778387562852665691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3698091704516750470220921 2773568778387562852665691)
        ·
          refine ⟨4160353167581344278998537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2773568778387562852665691 4160353167581344278998537)
          ·
            refine ⟨3120264875686008209248903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4160353167581344278998537 3120264875686008209248903)
            ·
              refine ⟨4680397313529012313873355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3120264875686008209248903 4680397313529012313873355)
              ·
                refine ⟨7020595970293518470810033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680397313529012313873355 7020595970293518470810033)
                ·
                  refine ⟨5265446977720138853107525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7020595970293518470810033 5265446977720138853107525)
                  ·
                    refine ⟨987271308322526034957661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5265446977720138853107525 987271308322526034957661)
                    ·
                      refine ⟨370226740620947263109123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 987271308322526034957661 370226740620947263109123)
                      ·
                        rfl

theorem cell23_721014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_721014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721014 prefixEnd_721014 := by exact prefixLift 721014
  have htrace : WordTrace (prefixWord ++ tailWord_721014) baseStart_721014 baseEnd_721014 := by
    simpa [prefixWord, tailWord_721014, baseEnd_721014] using wordTrace_append hprefix tailTrace_721014
  have hstable : (prefixWord ++ tailWord_721014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721014).length < 2 ^ (prefixWord ++ tailWord_721014).sum := by decide
  have hdescent : baseEnd_721014 < baseStart_721014 := by decide
  rcases family_descends (prefixWord ++ tailWord_721014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721027 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 3]
def baseStart_721027 : Nat := 118140960795 + 721027 * 2 ^ 59
def prefixEnd_721027 : Nat := 4983230072969 + 3 ^ 40 * 721027 * 2
def baseEnd_721027 : Nat := 370233415869455712246563

theorem tailTrace_721027 : CollatzResearch.WordTrace tailWord_721027 prefixEnd_721027 370233415869455712246563 := by
  unfold tailWord_721027
  simp only [CollatzResearch.WordTrace]
  refine ⟨26298015158849795452905335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17532010105899863635270223 26298015158849795452905335)
  ·
    refine ⟨39447022738274693179358003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26298015158849795452905335 39447022738274693179358003)
    ·
      refine ⟨59170534107412039769037005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39447022738274693179358003 59170534107412039769037005)
      ·
        refine ⟨22188950290279514913388877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59170534107412039769037005 22188950290279514913388877)
        ·
          refine ⟨8320856358854818092520829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22188950290279514913388877 8320856358854818092520829)
          ·
            refine ⟨3120321134570556784695311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8320856358854818092520829 3120321134570556784695311)
            ·
              refine ⟨4680481701855835177042967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3120321134570556784695311 4680481701855835177042967)
              ·
                refine ⟨7020722552783752765564451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680481701855835177042967 7020722552783752765564451)
                ·
                  refine ⟨10531083829175629148346677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7020722552783752765564451 10531083829175629148346677)
                  ·
                    refine ⟨987289108985215232657501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10531083829175629148346677 987289108985215232657501)
                    ·
                      refine ⟨370233415869455712246563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 987289108985215232657501 370233415869455712246563)
                      ·
                        rfl

theorem cell23_721027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_721027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721027 prefixEnd_721027 := by exact prefixLift 721027
  have htrace : WordTrace (prefixWord ++ tailWord_721027) baseStart_721027 baseEnd_721027 := by
    simpa [prefixWord, tailWord_721027, baseEnd_721027] using wordTrace_append hprefix tailTrace_721027
  have hstable : (prefixWord ++ tailWord_721027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721027).length < 2 ^ (prefixWord ++ tailWord_721027).sum := by decide
  have hdescent : baseEnd_721027 < baseStart_721027 := by decide
  rcases family_descends (prefixWord ++ tailWord_721027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721144 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 3, 5, 2]
def baseStart_721144 : Nat := 118140960795 + 721144 * 2 ^ 59
def prefixEnd_721144 : Nat := 4983230072969 + 3 ^ 40 * 721144 * 2
def baseEnd_721144 : Nat := 370293493106031754483525

theorem tailTrace_721144 : CollatzResearch.WordTrace tailWord_721144 prefixEnd_721144 370293493106031754483525 := by
  unfold tailWord_721144
  simp only [CollatzResearch.WordTrace]
  refine ⟨13151141249712962217457243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17534854999617282956609657 13151141249712962217457243)
  ·
    refine ⟨19726711874569443326185865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13151141249712962217457243 19726711874569443326185865)
    ·
      refine ⟨14795033905927082494639399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19726711874569443326185865 14795033905927082494639399)
      ·
        refine ⟨22192550858890623741959099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14795033905927082494639399 22192550858890623741959099)
        ·
          refine ⟨33288826288335935612938649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22192550858890623741959099 33288826288335935612938649)
          ·
            refine ⟨24966619716251951709703987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33288826288335935612938649 24966619716251951709703987)
            ·
              refine ⟨37449929574377927564555981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24966619716251951709703987 37449929574377927564555981)
              ·
                refine ⟨14043723590391722836708493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37449929574377927564555981 14043723590391722836708493)
                ·
                  refine ⟨5266396346396896063765685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14043723590391722836708493 5266396346396896063765685)
                  ·
                    refine ⟨493724657474709005978033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5266396346396896063765685 493724657474709005978033)
                    ·
                      refine ⟨370293493106031754483525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 493724657474709005978033 370293493106031754483525)
                      ·
                        rfl

theorem cell23_721144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 3, 5, 2].length) (baseStart_721144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721144 prefixEnd_721144 := by exact prefixLift 721144
  have htrace : WordTrace (prefixWord ++ tailWord_721144) baseStart_721144 baseEnd_721144 := by
    simpa [prefixWord, tailWord_721144, baseEnd_721144] using wordTrace_append hprefix tailTrace_721144
  have hstable : (prefixWord ++ tailWord_721144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721144).length < 2 ^ (prefixWord ++ tailWord_721144).sum := by decide
  have hdescent : baseEnd_721144 < baseStart_721144 := by decide
  rcases family_descends (prefixWord ++ tailWord_721144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721161 : List Nat := [1, 2, 1, 1, 3, 4, 1, 3, 2, 3, 2]
def baseStart_721161 : Nat := 118140960795 + 721161 * 2 ^ 59
def prefixEnd_721161 : Nat := 4983230072969 + 3 ^ 40 * 721161 * 2
def baseEnd_721161 : Nat := 370302222277158187970947

theorem tailTrace_721161 : CollatzResearch.WordTrace tailWord_721161 prefixEnd_721161 370302222277158187970947 := by
  unfold tailWord_721161
  simp only [CollatzResearch.WordTrace]
  refine ⟨26302902540364336338283337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17535268360242890892188891 26302902540364336338283337)
  ·
    refine ⟨19727176905273252253712503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26302902540364336338283337 19727176905273252253712503)
    ·
      refine ⟨29590765357909878380568755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19727176905273252253712503 29590765357909878380568755)
      ·
        refine ⟨44386148036864817570853133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29590765357909878380568755 44386148036864817570853133)
        ·
          refine ⟨16644805513824306589069925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44386148036864817570853133 16644805513824306589069925)
          ·
            refine ⟨3120901033842057485450611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16644805513824306589069925 3120901033842057485450611)
            ·
              refine ⟨4681351550763086228175917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3120901033842057485450611 4681351550763086228175917)
              ·
                refine ⟨1755506831536157335565969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4681351550763086228175917 1755506831536157335565969)
                ·
                  refine ⟨1316630123652118001674477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1755506831536157335565969 1316630123652118001674477)
                  ·
                    refine ⟨493736296369544250627929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1316630123652118001674477 493736296369544250627929)
                    ·
                      refine ⟨370302222277158187970947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 493736296369544250627929 370302222277158187970947)
                      ·
                        rfl

theorem cell23_721161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 3, 2].length) (baseStart_721161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721161 prefixEnd_721161 := by exact prefixLift 721161
  have htrace : WordTrace (prefixWord ++ tailWord_721161) baseStart_721161 baseEnd_721161 := by
    simpa [prefixWord, tailWord_721161, baseEnd_721161] using wordTrace_append hprefix tailTrace_721161
  have hstable : (prefixWord ++ tailWord_721161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721161).length < 2 ^ (prefixWord ++ tailWord_721161).sum := by decide
  have hdescent : baseEnd_721161 < baseStart_721161 := by decide
  rcases family_descends (prefixWord ++ tailWord_721161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721185 : List Nat := [1, 2, 3, 2, 1, 1, 6, 2, 1, 1, 3]
def baseStart_721185 : Nat := 118140960795 + 721185 * 2 ^ 59
def prefixEnd_721185 : Nat := 4983230072969 + 3 ^ 40 * 721185 * 2
def baseEnd_721185 : Nat := 370314545812866094070837

theorem tailTrace_721185 : CollatzResearch.WordTrace tailWord_721185 prefixEnd_721185 370314545812866094070837 := by
  unfold tailWord_721185
  simp only [CollatzResearch.WordTrace]
  refine ⟨26303777892277388437157009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17535851928184925624771339 26303777892277388437157009)
  ·
    refine ⟨19727833419208041327867757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26303777892277388437157009 19727833419208041327867757)
    ·
      refine ⟨7397937532203015497950409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19727833419208041327867757 7397937532203015497950409)
      ·
        refine ⟨5548453149152261623462807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7397937532203015497950409 5548453149152261623462807)
        ·
          refine ⟨8322679723728392435194211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5548453149152261623462807 8322679723728392435194211)
          ·
            refine ⟨12484019585592588652791317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8322679723728392435194211 12484019585592588652791317)
            ·
              refine ⟨585188418074652593099593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12484019585592588652791317 585188418074652593099593)
              ·
                refine ⟨438891313555989444824695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585188418074652593099593 438891313555989444824695)
                ·
                  refine ⟨658336970333984167237043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438891313555989444824695 658336970333984167237043)
                  ·
                    refine ⟨987505455500976250855565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 658336970333984167237043 987505455500976250855565)
                    ·
                      refine ⟨370314545812866094070837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 987505455500976250855565 370314545812866094070837)
                      ·
                        rfl

theorem cell23_721185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_721185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721185 prefixEnd_721185 := by exact prefixLift 721185
  have htrace : WordTrace (prefixWord ++ tailWord_721185) baseStart_721185 baseEnd_721185 := by
    simpa [prefixWord, tailWord_721185, baseEnd_721185] using wordTrace_append hprefix tailTrace_721185
  have hstable : (prefixWord ++ tailWord_721185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721185).length < 2 ^ (prefixWord ++ tailWord_721185).sum := by decide
  have hdescent : baseEnd_721185 < baseStart_721185 := by decide
  rcases family_descends (prefixWord ++ tailWord_721185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721201 : List Nat := [1, 2, 2, 3, 4, 1, 2, 1, 1, 6]
def baseStart_721201 : Nat := 118140960795 + 721201 * 2 ^ 59
def prefixEnd_721201 : Nat := 4983230072969 + 3 ^ 40 * 721201 * 2
def baseEnd_721201 : Nat := 123440920501112677156921

theorem tailTrace_721201 : CollatzResearch.WordTrace tailWord_721201 prefixEnd_721201 123440920501112677156921 := by
  unfold tailWord_721201
  simp only [CollatzResearch.WordTrace]
  refine ⟨26304361460219423169739457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17536240973479615446492971 26304361460219423169739457)
  ·
    refine ⟨19728271095164567377304593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26304361460219423169739457 19728271095164567377304593)
    ·
      refine ⟨14796203321373425532978445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19728271095164567377304593 14796203321373425532978445)
      ·
        refine ⟨5548576245515034574866917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14796203321373425532978445 5548576245515034574866917)
        ·
          refine ⟨1040358046034068982787547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5548576245515034574866917 1040358046034068982787547)
          ·
            refine ⟨1560537069051103474181321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040358046034068982787547 1560537069051103474181321)
            ·
              refine ⟨1170402801788327605635991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1560537069051103474181321 1170402801788327605635991)
              ·
                refine ⟨1755604202682491408453987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1170402801788327605635991 1755604202682491408453987)
                ·
                  refine ⟨2633406304023737112680981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1755604202682491408453987 2633406304023737112680981)
                  ·
                    refine ⟨123440920501112677156921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2633406304023737112680981 123440920501112677156921)
                    ·
                      rfl

theorem cell23_721201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_721201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721201 prefixEnd_721201 := by exact prefixLift 721201
  have htrace : WordTrace (prefixWord ++ tailWord_721201) baseStart_721201 baseEnd_721201 := by
    simpa [prefixWord, tailWord_721201, baseEnd_721201] using wordTrace_append hprefix tailTrace_721201
  have hstable : (prefixWord ++ tailWord_721201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721201).length < 2 ^ (prefixWord ++ tailWord_721201).sum := by decide
  have hdescent : baseEnd_721201 < baseStart_721201 := by decide
  rcases family_descends (prefixWord ++ tailWord_721201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721207 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 7]
def baseStart_721207 : Nat := 118140960795 + 721207 * 2 ^ 59
def prefixEnd_721207 : Nat := 4983230072969 + 3 ^ 40 * 721207 * 2
def baseEnd_721207 : Nat := 370325842387265007995735

theorem tailTrace_721207 : CollatzResearch.WordTrace tailWord_721207 prefixEnd_721207 370325842387265007995735 := by
  unfold tailWord_721207
  simp only [CollatzResearch.WordTrace]
  refine ⟨26304580298197686194457875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17536386865465124129638583 26304580298197686194457875)
  ·
    refine ⟨39456870447296529291686813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26304580298197686194457875 39456870447296529291686813)
    ·
      refine ⟨14796326417736198484382555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39456870447296529291686813 14796326417736198484382555)
      ·
        refine ⟨22194489626604297726573833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14796326417736198484382555 22194489626604297726573833)
        ·
          refine ⟨16645867219953223294930375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22194489626604297726573833 16645867219953223294930375)
          ·
            refine ⟨24968800829929834942395563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16645867219953223294930375 24968800829929834942395563)
            ·
              refine ⟨37453201244894752413593345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24968800829929834942395563 37453201244894752413593345)
              ·
                refine ⟨28089900933671064310195009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37453201244894752413593345 28089900933671064310195009)
                ·
                  refine ⟨21067425700253298232646257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28089900933671064310195009 21067425700253298232646257)
                  ·
                    refine ⟨15800569275189973674484693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21067425700253298232646257 15800569275189973674484693)
                    ·
                      refine ⟨370325842387265007995735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15800569275189973674484693 370325842387265007995735)
                      ·
                        rfl

theorem cell23_721207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_721207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721207 prefixEnd_721207 := by exact prefixLift 721207
  have htrace : WordTrace (prefixWord ++ tailWord_721207) baseStart_721207 baseEnd_721207 := by
    simpa [prefixWord, tailWord_721207, baseEnd_721207] using wordTrace_append hprefix tailTrace_721207
  have hstable : (prefixWord ++ tailWord_721207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721207).length < 2 ^ (prefixWord ++ tailWord_721207).sum := by decide
  have hdescent : baseEnd_721207 < baseStart_721207 := by decide
  rcases family_descends (prefixWord ++ tailWord_721207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721227 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 1, 9]
def baseStart_721227 : Nat := 118140960795 + 721227 * 2 ^ 59
def prefixEnd_721227 : Nat := 4983230072969 + 3 ^ 40 * 721227 * 2
def baseEnd_721227 : Nat := 123445370666784976581881

theorem tailTrace_721227 : CollatzResearch.WordTrace tailWord_721227 prefixEnd_721227 123445370666784976581881 := by
  unfold tailWord_721227
  simp only [CollatzResearch.WordTrace]
  refine ⟨26305309758125229610185935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17536873172083486406790623 26305309758125229610185935)
  ·
    refine ⟨39457964637187844415278903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26305309758125229610185935 39457964637187844415278903)
    ·
      refine ⟨59186946955781766622918355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39457964637187844415278903 59186946955781766622918355)
      ·
        refine ⟨88780420433672649934377533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59186946955781766622918355 88780420433672649934377533)
        ·
          refine ⟨33292657662627243725391575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88780420433672649934377533 33292657662627243725391575)
          ·
            refine ⟨49938986493940865588087363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33292657662627243725391575 49938986493940865588087363)
            ·
              refine ⟨74908479740911298382131045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49938986493940865588087363 74908479740911298382131045)
              ·
                refine ⟨14045339951420868446649571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74908479740911298382131045 14045339951420868446649571)
                ·
                  refine ⟨21068009927131302669974357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14045339951420868446649571 21068009927131302669974357)
                  ·
                    refine ⟨123445370666784976581881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 21068009927131302669974357 123445370666784976581881)
                    ·
                      rfl

theorem cell23_721227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 9].length) (baseStart_721227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721227 prefixEnd_721227 := by exact prefixLift 721227
  have htrace : WordTrace (prefixWord ++ tailWord_721227) baseStart_721227 baseEnd_721227 := by
    simpa [prefixWord, tailWord_721227, baseEnd_721227] using wordTrace_append hprefix tailTrace_721227
  have hstable : (prefixWord ++ tailWord_721227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721227).length < 2 ^ (prefixWord ++ tailWord_721227).sum := by decide
  have hdescent : baseEnd_721227 < baseStart_721227 := by decide
  rcases family_descends (prefixWord ++ tailWord_721227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721258 : List Nat := [3, 1, 3, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_721258 : Nat := 118140960795 + 721258 * 2 ^ 59
def prefixEnd_721258 : Nat := 4983230072969 + 3 ^ 40 * 721258 * 2
def baseEnd_721258 : Nat := 370352029900644308458001

theorem tailTrace_721258 : CollatzResearch.WordTrace tailWord_721258 prefixEnd_721258 370352029900644308458001 := by
  unfold tailWord_721258
  simp only [CollatzResearch.WordTrace]
  refine ⟨6576610105253230476141107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17537626947341947936376285 6576610105253230476141107)
  ·
    refine ⟨9864915157879845714211661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6576610105253230476141107 9864915157879845714211661)
    ·
      refine ⟨3699343184204942142829373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9864915157879845714211661 3699343184204942142829373)
      ·
        refine ⟨1387253694076853303561015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3699343184204942142829373 1387253694076853303561015)
        ·
          refine ⟨2080880541115279955341523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1387253694076853303561015 2080880541115279955341523)
          ·
            refine ⟨3121320811672919933012285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080880541115279955341523 3121320811672919933012285)
            ·
              refine ⟨1170495304377344974879607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3121320811672919933012285 1170495304377344974879607)
              ·
                refine ⟨1755742956566017462319411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1170495304377344974879607 1755742956566017462319411)
                ·
                  refine ⟨2633614434849026193479117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1755742956566017462319411 2633614434849026193479117)
                  ·
                    refine ⟨987605413068384822554669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2633614434849026193479117 987605413068384822554669)
                    ·
                      refine ⟨370352029900644308458001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 987605413068384822554669 370352029900644308458001)
                      ·
                        rfl

theorem cell23_721258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_721258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721258 prefixEnd_721258 := by exact prefixLift 721258
  have htrace : WordTrace (prefixWord ++ tailWord_721258) baseStart_721258 baseEnd_721258 := by
    simpa [prefixWord, tailWord_721258, baseEnd_721258] using wordTrace_append hprefix tailTrace_721258
  have hstable : (prefixWord ++ tailWord_721258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721258).length < 2 ^ (prefixWord ++ tailWord_721258).sum := by decide
  have hdescent : baseEnd_721258 < baseStart_721258 := by decide
  rcases family_descends (prefixWord ++ tailWord_721258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721309 : List Nat := [1, 4, 2, 1, 5, 1, 2, 1, 2, 1, 3]
def baseStart_721309 : Nat := 118140960795 + 721309 * 2 ^ 59
def prefixEnd_721309 : Nat := 4983230072969 + 3 ^ 40 * 721309 * 2
def baseEnd_721309 : Nat := 370378217414023608920267

theorem tailTrace_721309 : CollatzResearch.WordTrace tailWord_721309 prefixEnd_721309 370378217414023608920267 := by
  unfold tailWord_721309
  simp only [CollatzResearch.WordTrace]
  refine ⟨26308300543828157614670981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17538867029218771743113987 26308300543828157614670981)
  ·
    refine ⟨4932806351967779552750809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26308300543828157614670981 4932806351967779552750809)
    ·
      refine ⟨3699604763975834664563107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4932806351967779552750809 3699604763975834664563107)
      ·
        refine ⟨5549407145963751996844661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3699604763975834664563107 5549407145963751996844661)
        ·
          refine ⟨520256919934101749704187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5549407145963751996844661 520256919934101749704187)
          ·
            refine ⟨780385379901152624556281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520256919934101749704187 780385379901152624556281)
            ·
              refine ⟨585289034925864468417211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 780385379901152624556281 585289034925864468417211)
              ·
                refine ⟨877933552388796702625817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585289034925864468417211 877933552388796702625817)
                ·
                  refine ⟨658450164291597526969363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 877933552388796702625817 658450164291597526969363)
                  ·
                    refine ⟨987675246437396290454045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 658450164291597526969363 987675246437396290454045)
                    ·
                      refine ⟨370378217414023608920267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 987675246437396290454045 370378217414023608920267)
                      ·
                        rfl

theorem cell23_721309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_721309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721309 prefixEnd_721309 := by exact prefixLift 721309
  have htrace : WordTrace (prefixWord ++ tailWord_721309) baseStart_721309 baseEnd_721309 := by
    simpa [prefixWord, tailWord_721309, baseEnd_721309] using wordTrace_append hprefix tailTrace_721309
  have hstable : (prefixWord ++ tailWord_721309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721309).length < 2 ^ (prefixWord ++ tailWord_721309).sum := by decide
  have hdescent : baseEnd_721309 < baseStart_721309 := by decide
  rcases family_descends (prefixWord ++ tailWord_721309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721315 : List Nat := [1, 1, 1, 4, 1, 5, 1, 3, 2, 2, 2]
def baseStart_721315 : Nat := 118140960795 + 721315 * 2 ^ 59
def prefixEnd_721315 : Nat := 4983230072969 + 3 ^ 40 * 721315 * 2
def baseEnd_721315 : Nat := 370381298297950585445239

theorem tailTrace_721315 : CollatzResearch.WordTrace tailWord_721315 prefixEnd_721315 370381298297950585445239 := by
  unfold tailWord_721315
  simp only [CollatzResearch.WordTrace]
  refine ⟨26308519381806420639389399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17539012921204280426259599 26308519381806420639389399)
  ·
    refine ⟨39462779072709630959084099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26308519381806420639389399 39462779072709630959084099)
    ·
      refine ⟨59194168609064446438626149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39462779072709630959084099 59194168609064446438626149)
      ·
        refine ⟨11098906614199583707242403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59194168609064446438626149 11098906614199583707242403)
        ·
          refine ⟨16648359921299375560863605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11098906614199583707242403 16648359921299375560863605)
          ·
            refine ⟨1560783742621816458830963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16648359921299375560863605 1560783742621816458830963)
            ·
              refine ⟨2341175613932724688246445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1560783742621816458830963 2341175613932724688246445)
              ·
                refine ⟨877940855224771758092417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2341175613932724688246445 877940855224771758092417)
                ·
                  refine ⟨658455641418578818569313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 877940855224771758092417 658455641418578818569313)
                  ·
                    refine ⟨493841731063934113926985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 658455641418578818569313 493841731063934113926985)
                    ·
                      refine ⟨370381298297950585445239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 493841731063934113926985 370381298297950585445239)
                      ·
                        rfl

theorem cell23_721315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_721315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721315 prefixEnd_721315 := by exact prefixLift 721315
  have htrace : WordTrace (prefixWord ++ tailWord_721315) baseStart_721315 baseEnd_721315 := by
    simpa [prefixWord, tailWord_721315, baseEnd_721315] using wordTrace_append hprefix tailTrace_721315
  have hstable : (prefixWord ++ tailWord_721315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721315).length < 2 ^ (prefixWord ++ tailWord_721315).sum := by decide
  have hdescent : baseEnd_721315 < baseStart_721315 := by decide
  rcases family_descends (prefixWord ++ tailWord_721315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721351 : List Nat := [1, 1, 4, 1, 1, 4, 2, 2, 2, 5]
def baseStart_721351 : Nat := 118140960795 + 721351 * 2 ^ 59
def prefixEnd_721351 : Nat := 4983230072969 + 3 ^ 40 * 721351 * 2
def baseEnd_721351 : Nat := 123466594533837481531691

theorem tailTrace_721351 : CollatzResearch.WordTrace tailWord_721351 prefixEnd_721351 123466594533837481531691 := by
  unfold tailWord_721351
  simp only [CollatzResearch.WordTrace]
  refine ⟨26309832409675998787699907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17539888273117332525133271 26309832409675998787699907)
  ·
    refine ⟨39464748614513998181549861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26309832409675998787699907 39464748614513998181549861)
    ·
      refine ⟨7399640365221374659040599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39464748614513998181549861 7399640365221374659040599)
      ·
        refine ⟨11099460547832061988560899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7399640365221374659040599 11099460547832061988560899)
        ·
          refine ⟨16649190821748092982841349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11099460547832061988560899 16649190821748092982841349)
          ·
            refine ⟨3121723279077767434282753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16649190821748092982841349 3121723279077767434282753)
            ·
              refine ⟨2341292459308325575712065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3121723279077767434282753 2341292459308325575712065)
              ·
                refine ⟨1755969344481244181784049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2341292459308325575712065 1755969344481244181784049)
                ·
                  refine ⟨1316977008360933136338037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1755969344481244181784049 1316977008360933136338037)
                  ·
                    refine ⟨123466594533837481531691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1316977008360933136338037 123466594533837481531691)
                    ·
                      rfl

theorem cell23_721351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_721351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721351 prefixEnd_721351 := by exact prefixLift 721351
  have htrace : WordTrace (prefixWord ++ tailWord_721351) baseStart_721351 baseEnd_721351 := by
    simpa [prefixWord, tailWord_721351, baseEnd_721351] using wordTrace_append hprefix tailTrace_721351
  have hstable : (prefixWord ++ tailWord_721351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721351).length < 2 ^ (prefixWord ++ tailWord_721351).sum := by decide
  have hdescent : baseEnd_721351 < baseStart_721351 := by decide
  rcases family_descends (prefixWord ++ tailWord_721351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721398 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_721398 : Nat := 118140960795 + 721398 * 2 ^ 59
def prefixEnd_721398 : Nat := 4983230072969 + 3 ^ 40 * 721398 * 2
def baseEnd_721398 : Nat := 123474639064091253569119

theorem tailTrace_721398 : CollatzResearch.WordTrace tailWord_721398 prefixEnd_721398 123474639064091253569119 := by
  unfold tailWord_721398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1644471665031607863416303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17541031093670483876440565 1644471665031607863416303)
  ·
    refine ⟨2466707497547411795124455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1644471665031607863416303 2466707497547411795124455)
    ·
      refine ⟨3700061246321117692686683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2466707497547411795124455 3700061246321117692686683)
      ·
        refine ⟨5550091869481676539030025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3700061246321117692686683 5550091869481676539030025)
        ·
          refine ⟨4162568902111257404272519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5550091869481676539030025 4162568902111257404272519)
          ·
            refine ⟨6243853353166886106408779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162568902111257404272519 6243853353166886106408779)
            ·
              refine ⟨9365780029750329159613169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6243853353166886106408779 9365780029750329159613169)
              ·
                refine ⟨7024335022312746869709877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9365780029750329159613169 7024335022312746869709877)
                ·
                  refine ⟨658531408341820019035301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7024335022312746869709877 658531408341820019035301)
                  ·
                    refine ⟨123474639064091253569119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 658531408341820019035301 123474639064091253569119)
                    ·
                      rfl

theorem cell23_721398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_721398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721398 prefixEnd_721398 := by exact prefixLift 721398
  have htrace : WordTrace (prefixWord ++ tailWord_721398) baseStart_721398 baseEnd_721398 := by
    simpa [prefixWord, tailWord_721398, baseEnd_721398] using wordTrace_append hprefix tailTrace_721398
  have hstable : (prefixWord ++ tailWord_721398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721398).length < 2 ^ (prefixWord ++ tailWord_721398).sum := by decide
  have hdescent : baseEnd_721398 < baseStart_721398 := by decide
  rcases family_descends (prefixWord ++ tailWord_721398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721415 : List Nat := [1, 1, 4, 3, 3, 1, 2, 1, 3, 4]
def baseStart_721415 : Nat := 118140960795 + 721415 * 2 ^ 59
def prefixEnd_721415 : Nat := 4983230072969 + 3 ^ 40 * 721415 * 2
def baseEnd_721415 : Nat := 123477548787800064731593

theorem tailTrace_721415 : CollatzResearch.WordTrace tailWord_721415 prefixEnd_721415 123477548787800064731593 := by
  unfold tailWord_721415
  simp only [CollatzResearch.WordTrace]
  refine ⟨26312166681444137718029699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17541444454296091812019799 26312166681444137718029699)
  ·
    refine ⟨39468250022166206577044549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26312166681444137718029699 39468250022166206577044549)
    ·
      refine ⟨7400296879156163733195853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39468250022166206577044549 7400296879156163733195853)
      ·
        refine ⟨2775111329683561399948445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7400296879156163733195853 2775111329683561399948445)
        ·
          refine ⟨1040666748631335524980667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2775111329683561399948445 1040666748631335524980667)
          ·
            refine ⟨1561000122947003287471001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040666748631335524980667 1561000122947003287471001)
            ·
              refine ⟨1170750092210252465603251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1561000122947003287471001 1170750092210252465603251)
              ·
                refine ⟨1756125138315378698404877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1170750092210252465603251 1756125138315378698404877)
                ·
                  refine ⟨658546926868267011901829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1756125138315378698404877 658546926868267011901829)
                  ·
                    refine ⟨123477548787800064731593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 658546926868267011901829 123477548787800064731593)
                    ·
                      rfl

theorem cell23_721415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_721415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721415 prefixEnd_721415 := by exact prefixLift 721415
  have htrace : WordTrace (prefixWord ++ tailWord_721415) baseStart_721415 baseEnd_721415 := by
    simpa [prefixWord, tailWord_721415, baseEnd_721415] using wordTrace_append hprefix tailTrace_721415
  have hstable : (prefixWord ++ tailWord_721415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721415).length < 2 ^ (prefixWord ++ tailWord_721415).sum := by decide
  have hdescent : baseEnd_721415 < baseStart_721415 := by decide
  rcases family_descends (prefixWord ++ tailWord_721415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721458 : List Nat := [3, 2, 1, 1, 2, 1, 4, 3, 1, 5]
def baseStart_721458 : Nat := 118140960795 + 721458 * 2 ^ 59
def prefixEnd_721458 : Nat := 4983230072969 + 3 ^ 40 * 721458 * 2
def baseEnd_721458 : Nat := 123484908677181175319027

theorem tailTrace_721458 : CollatzResearch.WordTrace tailWord_721458 prefixEnd_721458 123484908677181175319027 := by
  unfold tailWord_721458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6578433755072089015461257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17542490013525570707896685 6578433755072089015461257)
  ·
    refine ⟨4933825316304066761595943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6578433755072089015461257 4933825316304066761595943)
    ·
      refine ⟨7400737974456100142393915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4933825316304066761595943 7400737974456100142393915)
      ·
        refine ⟨11101106961684150213590873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7400737974456100142393915 11101106961684150213590873)
        ·
          refine ⟨8325830221263112660193155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11101106961684150213590873 8325830221263112660193155)
          ·
            refine ⟨12488745331894668990289733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8325830221263112660193155 12488745331894668990289733)
            ·
              refine ⟨2341639749730250435679325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12488745331894668990289733 2341639749730250435679325)
              ·
                refine ⟨878114906148843913379747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2341639749730250435679325 878114906148843913379747)
                ·
                  refine ⟨1317172359223265870069621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 878114906148843913379747 1317172359223265870069621)
                  ·
                    refine ⟨123484908677181175319027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1317172359223265870069621 123484908677181175319027)
                    ·
                      rfl

theorem cell23_721458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_721458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721458 prefixEnd_721458 := by exact prefixLift 721458
  have htrace : WordTrace (prefixWord ++ tailWord_721458) baseStart_721458 baseEnd_721458 := by
    simpa [prefixWord, tailWord_721458, baseEnd_721458] using wordTrace_append hprefix tailTrace_721458
  have hstable : (prefixWord ++ tailWord_721458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721458).length < 2 ^ (prefixWord ++ tailWord_721458).sum := by decide
  have hdescent : baseEnd_721458 < baseStart_721458 := by decide
  rcases family_descends (prefixWord ++ tailWord_721458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721465 : List Nat := [1, 2, 1, 5, 1, 1, 3, 2, 2, 3, 2]
def baseStart_721465 : Nat := 118140960795 + 721465 * 2 ^ 59
def prefixEnd_721465 : Nat := 4983230072969 + 3 ^ 40 * 721465 * 2
def baseEnd_721465 : Nat := 370458320396124998569549

theorem tailTrace_721465 : CollatzResearch.WordTrace tailWord_721465 prefixEnd_721465 370458320396124998569549 := by
  unfold tailWord_721465
  simp only [CollatzResearch.WordTrace]
  refine ⟨26313990331262996257349849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17542660220841997504899899 26313990331262996257349849)
  ·
    refine ⟨19735492748447247193012387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26313990331262996257349849 19735492748447247193012387)
    ·
      refine ⟨29603239122670870789518581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19735492748447247193012387 29603239122670870789518581)
      ·
        refine ⟨2775303667750394136517367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29603239122670870789518581 2775303667750394136517367)
        ·
          refine ⟨4162955501625591204776051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2775303667750394136517367 4162955501625591204776051)
          ·
            refine ⟨6244433252438386807164077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162955501625591204776051 6244433252438386807164077)
            ·
              refine ⟨2341662469664395052686529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6244433252438386807164077 2341662469664395052686529)
              ·
                refine ⟨1756246852248296289514897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2341662469664395052686529 1756246852248296289514897)
                ·
                  refine ⟨1317185139186222217136173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1756246852248296289514897 1317185139186222217136173)
                  ·
                    refine ⟨493944427194833331426065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1317185139186222217136173 493944427194833331426065)
                    ·
                      refine ⟨370458320396124998569549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 493944427194833331426065 370458320396124998569549)
                      ·
                        rfl

theorem cell23_721465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_721465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721465 prefixEnd_721465 := by exact prefixLift 721465
  have htrace : WordTrace (prefixWord ++ tailWord_721465) baseStart_721465 baseEnd_721465 := by
    simpa [prefixWord, tailWord_721465, baseEnd_721465] using wordTrace_append hprefix tailTrace_721465
  have hstable : (prefixWord ++ tailWord_721465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721465).length < 2 ^ (prefixWord ++ tailWord_721465).sum := by decide
  have hdescent : baseEnd_721465 < baseStart_721465 := by decide
  rcases family_descends (prefixWord ++ tailWord_721465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721481 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 1, 8, 3]
def baseStart_721481 : Nat := 118140960795 + 721481 * 2 ^ 59
def prefixEnd_721481 : Nat := 4983230072969 + 3 ^ 40 * 721481 * 2
def baseEnd_721481 : Nat := 370466536086596935969475

theorem tailTrace_721481 : CollatzResearch.WordTrace tailWord_721481 prefixEnd_721481 370466536086596935969475 := by
  unfold tailWord_721481
  simp only [CollatzResearch.WordTrace]
  refine ⟨26314573899205030989932297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17543049266136687326621531 26314573899205030989932297)
  ·
    refine ⟨19735930424403773242449223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26314573899205030989932297 19735930424403773242449223)
    ·
      refine ⟨29603895636605659863673835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19735930424403773242449223 29603895636605659863673835)
      ·
        refine ⟨44405843454908489795510753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29603895636605659863673835 44405843454908489795510753)
        ·
          refine ⟨33304382591181367346633065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44405843454908489795510753 33304382591181367346633065)
          ·
            refine ⟨24978286943386025509974799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33304382591181367346633065 24978286943386025509974799)
            ·
              refine ⟨37467430415079038264962199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24978286943386025509974799 37467430415079038264962199)
              ·
                refine ⟨56201145622618557397443299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37467430415079038264962199 56201145622618557397443299)
                ·
                  refine ⟨84301718433927836096164949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56201145622618557397443299 84301718433927836096164949)
                  ·
                    refine ⟨987910762897591829251933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84301718433927836096164949 987910762897591829251933)
                    ·
                      refine ⟨370466536086596935969475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 987910762897591829251933 370466536086596935969475)
                      ·
                        rfl

theorem cell23_721481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 8, 3].length) (baseStart_721481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721481 prefixEnd_721481 := by exact prefixLift 721481
  have htrace : WordTrace (prefixWord ++ tailWord_721481) baseStart_721481 baseEnd_721481 := by
    simpa [prefixWord, tailWord_721481, baseEnd_721481] using wordTrace_append hprefix tailTrace_721481
  have hstable : (prefixWord ++ tailWord_721481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721481).length < 2 ^ (prefixWord ++ tailWord_721481).sum := by decide
  have hdescent : baseEnd_721481 < baseStart_721481 := by decide
  rcases family_descends (prefixWord ++ tailWord_721481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721495 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 5, 2, 2]
def baseStart_721495 : Nat := 118140960795 + 721495 * 2 ^ 59
def prefixEnd_721495 : Nat := 4983230072969 + 3 ^ 40 * 721495 * 2
def baseEnd_721495 : Nat := 370473724815759881194411

theorem tailTrace_721495 : CollatzResearch.WordTrace tailWord_721495 prefixEnd_721495 370473724815759881194411 := by
  unfold tailWord_721495
  simp only [CollatzResearch.WordTrace]
  refine ⟨26315084521154311380941939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17543389680769540920627959 26315084521154311380941939)
  ·
    refine ⟨39472626781731467071412909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26315084521154311380941939 39472626781731467071412909)
    ·
      refine ⟨14802235043149300151779841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39472626781731467071412909 14802235043149300151779841)
      ·
        refine ⟨11101676282361975113834881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14802235043149300151779841 11101676282361975113834881)
        ·
          refine ⟨8326257211771481335376161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11101676282361975113834881 8326257211771481335376161)
          ·
            refine ⟨6244692908828611001532121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8326257211771481335376161 6244692908828611001532121)
            ·
              refine ⟨4683519681621458251149091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6244692908828611001532121 4683519681621458251149091)
              ·
                refine ⟨7025279522432187376723637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4683519681621458251149091 7025279522432187376723637)
                ·
                  refine ⟨658619955228017566567841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7025279522432187376723637 658619955228017566567841)
                  ·
                    refine ⟨493964966421013174925881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 658619955228017566567841 493964966421013174925881)
                    ·
                      refine ⟨370473724815759881194411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 493964966421013174925881 370473724815759881194411)
                      ·
                        rfl

theorem cell23_721495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_721495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721495 prefixEnd_721495 := by exact prefixLift 721495
  have htrace : WordTrace (prefixWord ++ tailWord_721495) baseStart_721495 baseEnd_721495 := by
    simpa [prefixWord, tailWord_721495, baseEnd_721495] using wordTrace_append hprefix tailTrace_721495
  have hstable : (prefixWord ++ tailWord_721495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721495).length < 2 ^ (prefixWord ++ tailWord_721495).sum := by decide
  have hdescent : baseEnd_721495 < baseStart_721495 := by decide
  rcases family_descends (prefixWord ++ tailWord_721495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721508 : List Nat := [2, 3, 1, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_721508 : Nat := 118140960795 + 721508 * 2 ^ 59
def prefixEnd_721508 : Nat := 4983230072969 + 3 ^ 40 * 721508 * 2
def baseEnd_721508 : Nat := 370480400064268330331851

theorem tailTrace_721508 : CollatzResearch.WordTrace tailWord_721508 prefixEnd_721508 370480400064268330331851 := by
  unfold tailWord_721508
  simp only [CollatzResearch.WordTrace]
  refine ⟨13157779335053607300582589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17543705780071476400776785 13157779335053607300582589)
  ·
    refine ⟨4934167250645102737718471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13157779335053607300582589 4934167250645102737718471)
    ·
      refine ⟨7401250875967654106577707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4934167250645102737718471 7401250875967654106577707)
      ·
        refine ⟨11101876313951481159866561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7401250875967654106577707 11101876313951481159866561)
        ·
          refine ⟨8326407235463610869899921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11101876313951481159866561 8326407235463610869899921)
          ·
            refine ⟨6244805426597708152424941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8326407235463610869899921 6244805426597708152424941)
            ·
              refine ⟨2341802034974140557159353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6244805426597708152424941 2341802034974140557159353)
              ·
                refine ⟨1756351526230605417869515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2341802034974140557159353 1756351526230605417869515)
                ·
                  refine ⟨2634527289345908126804273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1756351526230605417869515 2634527289345908126804273)
                  ·
                    refine ⟨1975895467009431095103205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2634527289345908126804273 1975895467009431095103205)
                    ·
                      refine ⟨370480400064268330331851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1975895467009431095103205 370480400064268330331851)
                      ·
                        rfl

theorem cell23_721508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_721508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721508 prefixEnd_721508 := by exact prefixLift 721508
  have htrace : WordTrace (prefixWord ++ tailWord_721508) baseStart_721508 baseEnd_721508 := by
    simpa [prefixWord, tailWord_721508, baseEnd_721508] using wordTrace_append hprefix tailTrace_721508
  have hstable : (prefixWord ++ tailWord_721508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721508).length < 2 ^ (prefixWord ++ tailWord_721508).sum := by decide
  have hdescent : baseEnd_721508 < baseStart_721508 := by decide
  rcases family_descends (prefixWord ++ tailWord_721508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721522 : List Nat := [3, 2, 1, 2, 4, 1, 2, 2, 2, 4]
def baseStart_721522 : Nat := 118140960795 + 721522 * 2 ^ 59
def prefixEnd_721522 : Nat := 4983230072969 + 3 ^ 40 * 721522 * 2
def baseEnd_721522 : Nat := 123495862931143758518929

theorem tailTrace_721522 : CollatzResearch.WordTrace tailWord_721522 prefixEnd_721522 123495862931143758518929 := by
  unfold tailWord_721522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6579017323014123748043705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17544046194704329994783213 6579017323014123748043705)
  ·
    refine ⟨4934262992260592811032779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6579017323014123748043705 4934262992260592811032779)
    ·
      refine ⟨7401394488390889216549169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4934262992260592811032779 7401394488390889216549169)
      ·
        refine ⟨5551045866293166912411877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7401394488390889216549169 5551045866293166912411877)
        ·
          refine ⟨1040821099929968796077227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5551045866293166912411877 1040821099929968796077227)
          ·
            refine ⟨1561231649894953194115841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040821099929968796077227 1561231649894953194115841)
            ·
              refine ⟨1170923737421214895586881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1561231649894953194115841 1170923737421214895586881)
              ·
                refine ⟨878192803065911171690161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1170923737421214895586881 878192803065911171690161)
                ·
                  refine ⟨658644602299433378767621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 878192803065911171690161 658644602299433378767621)
                  ·
                    refine ⟨123495862931143758518929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 658644602299433378767621 123495862931143758518929)
                    ·
                      rfl

theorem cell23_721522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_721522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721522 prefixEnd_721522 := by exact prefixLift 721522
  have htrace : WordTrace (prefixWord ++ tailWord_721522) baseStart_721522 baseEnd_721522 := by
    simpa [prefixWord, tailWord_721522, baseEnd_721522] using wordTrace_append hprefix tailTrace_721522
  have hstable : (prefixWord ++ tailWord_721522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721522).length < 2 ^ (prefixWord ++ tailWord_721522).sum := by decide
  have hdescent : baseEnd_721522 < baseStart_721522 := by decide
  rcases family_descends (prefixWord ++ tailWord_721522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721529 : List Nat := [1, 2, 1, 3, 3, 3, 1, 4, 1, 2, 2]
def baseStart_721529 : Nat := 118140960795 + 721529 * 2 ^ 59
def prefixEnd_721529 : Nat := 4983230072969 + 3 ^ 40 * 721529 * 2
def baseEnd_721529 : Nat := 370491183158012748169255

theorem tailTrace_721529 : CollatzResearch.WordTrace tailWord_721529 prefixEnd_721529 370491183158012748169255 := by
  unfold tailWord_721529
  simp only [CollatzResearch.WordTrace]
  refine ⟨26316324603031135187679641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17544216402020756791786427 26316324603031135187679641)
  ·
    refine ⟨19737243452273351390759731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26316324603031135187679641 19737243452273351390759731)
    ·
      refine ⟨29605865178410027086139597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19737243452273351390759731 29605865178410027086139597)
      ·
        refine ⟨11102199441903760157302349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29605865178410027086139597 11102199441903760157302349)
        ·
          refine ⟨4163324790713910058988381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11102199441903760157302349 4163324790713910058988381)
          ·
            refine ⟨1561246796517716272120643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4163324790713910058988381 1561246796517716272120643)
            ·
              refine ⟨2341870194776574408180965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561246796517716272120643 2341870194776574408180965)
              ·
                refine ⟨439100661520607701533931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2341870194776574408180965 439100661520607701533931)
                ·
                  refine ⟨658650992280911552300897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439100661520607701533931 658650992280911552300897)
                  ·
                    refine ⟨493988244210683664225673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 658650992280911552300897 493988244210683664225673)
                    ·
                      refine ⟨370491183158012748169255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 493988244210683664225673 370491183158012748169255)
                      ·
                        rfl

theorem cell23_721529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 1, 2, 2].length) (baseStart_721529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721529 prefixEnd_721529 := by exact prefixLift 721529
  have htrace : WordTrace (prefixWord ++ tailWord_721529) baseStart_721529 baseEnd_721529 := by
    simpa [prefixWord, tailWord_721529, baseEnd_721529] using wordTrace_append hprefix tailTrace_721529
  have hstable : (prefixWord ++ tailWord_721529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721529).length < 2 ^ (prefixWord ++ tailWord_721529).sum := by decide
  have hdescent : baseEnd_721529 < baseStart_721529 := by decide
  rcases family_descends (prefixWord ++ tailWord_721529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721561 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 1, 8]
def baseStart_721561 : Nat := 118140960795 + 721561 * 2 ^ 59
def prefixEnd_721561 : Nat := 4983230072969 + 3 ^ 40 * 721561 * 2
def baseEnd_721561 : Nat := 123502538179652207656369

theorem tailTrace_721561 : CollatzResearch.WordTrace tailWord_721561 prefixEnd_721561 123502538179652207656369 := by
  unfold tailWord_721561
  simp only [CollatzResearch.WordTrace]
  refine ⟨26317491738915204652844537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17544994492610136435229691 26317491738915204652844537)
  ·
    refine ⟨19738118804186403489633403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26317491738915204652844537 19738118804186403489633403)
    ·
      refine ⟨29607178206279605234450105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19738118804186403489633403 29607178206279605234450105)
      ·
        refine ⟨22205383654709703925837579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29607178206279605234450105 22205383654709703925837579)
        ·
          refine ⟨33308075482064555888756369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22205383654709703925837579 33308075482064555888756369)
          ·
            refine ⟨24981056611548416916567277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33308075482064555888756369 24981056611548416916567277)
            ·
              refine ⟨9367896229330656343712729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24981056611548416916567277 9367896229330656343712729)
              ·
                refine ⟨7025922171997992257784547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9367896229330656343712729 7025922171997992257784547)
                ·
                  refine ⟨10538883257996988386676821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7025922171997992257784547 10538883257996988386676821)
                  ·
                    refine ⟨123502538179652207656369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10538883257996988386676821 123502538179652207656369)
                    ·
                      rfl

theorem cell23_721561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 8].length) (baseStart_721561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721561 prefixEnd_721561 := by exact prefixLift 721561
  have htrace : WordTrace (prefixWord ++ tailWord_721561) baseStart_721561 baseEnd_721561 := by
    simpa [prefixWord, tailWord_721561, baseEnd_721561] using wordTrace_append hprefix tailTrace_721561
  have hstable : (prefixWord ++ tailWord_721561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721561).length < 2 ^ (prefixWord ++ tailWord_721561).sum := by decide
  have hdescent : baseEnd_721561 < baseStart_721561 := by decide
  rcases family_descends (prefixWord ++ tailWord_721561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721572 : List Nat := [2, 3, 1, 2, 2, 1, 3, 3, 1, 3, 2]
def baseStart_721572 : Nat := 118140960795 + 721572 * 2 ^ 59
def prefixEnd_721572 : Nat := 4983230072969 + 3 ^ 40 * 721572 * 2
def baseEnd_721572 : Nat := 370513262826156079931557

theorem tailTrace_721572 : CollatzResearch.WordTrace tailWord_721572 prefixEnd_721572 370513262826156079931557 := by
  unfold tailWord_721572
  simp only [CollatzResearch.WordTrace]
  refine ⟨13158946470937676765747485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17545261961250235687663313 13158946470937676765747485)
  ·
    refine ⟨4934604926601628787155307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13158946470937676765747485 4934604926601628787155307)
    ·
      refine ⟨7401907389902443180732961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4934604926601628787155307 7401907389902443180732961)
      ·
        refine ⟨5551430542426832385549721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7401907389902443180732961 5551430542426832385549721)
        ·
          refine ⟨4163572906820124289162291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5551430542426832385549721 4163572906820124289162291)
          ·
            refine ⟨6245359360230186433743437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4163572906820124289162291 6245359360230186433743437)
            ·
              refine ⟨2342009760086319912653789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6245359360230186433743437 2342009760086319912653789)
              ·
                refine ⟨878253660032369967245171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2342009760086319912653789 878253660032369967245171)
                ·
                  refine ⟨1317380490048554950867757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 878253660032369967245171 1317380490048554950867757)
                  ·
                    refine ⟨494017683768208106575409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1317380490048554950867757 494017683768208106575409)
                    ·
                      refine ⟨370513262826156079931557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 494017683768208106575409 370513262826156079931557)
                      ·
                        rfl

theorem cell23_721572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_721572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721572 prefixEnd_721572 := by exact prefixLift 721572
  have htrace : WordTrace (prefixWord ++ tailWord_721572) baseStart_721572 baseEnd_721572 := by
    simpa [prefixWord, tailWord_721572, baseEnd_721572] using wordTrace_append hprefix tailTrace_721572
  have hstable : (prefixWord ++ tailWord_721572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721572).length < 2 ^ (prefixWord ++ tailWord_721572).sum := by decide
  have hdescent : baseEnd_721572 < baseStart_721572 := by decide
  rcases family_descends (prefixWord ++ tailWord_721572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721608 : List Nat := [2, 1, 3, 1, 2, 3, 2, 2, 7]
def baseStart_721608 : Nat := 118140960795 + 721608 * 2 ^ 59
def prefixEnd_721608 : Nat := 4983230072969 + 3 ^ 40 * 721608 * 2
def baseEnd_721608 : Nat := 41170194236635326564599

theorem tailTrace_721608 : CollatzResearch.WordTrace tailWord_721608 prefixEnd_721608 41170194236635326564599 := by
  unfold tailWord_721608
  simp only [CollatzResearch.WordTrace]
  refine ⟨13159602984872465839902739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17546137313163287786536985 13159602984872465839902739)
  ·
    refine ⟨19739404477308698759854109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13159602984872465839902739 19739404477308698759854109)
    ·
      refine ⟨7402276678990762034945291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19739404477308698759854109 7402276678990762034945291)
      ·
        refine ⟨11103415018486143052417937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7402276678990762034945291 11103415018486143052417937)
        ·
          refine ⟨8327561263864607289313453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11103415018486143052417937 8327561263864607289313453)
          ·
            refine ⟨3122835473949227733492545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8327561263864607289313453 3122835473949227733492545)
            ·
              refine ⟨2342126605461920800119409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3122835473949227733492545 2342126605461920800119409)
              ·
                refine ⟨1756594954096440600089557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2342126605461920800119409 1756594954096440600089557)
                ·
                  refine ⟨41170194236635326564599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1756594954096440600089557 41170194236635326564599)
                  ·
                    rfl

theorem cell23_721608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 7].length) (baseStart_721608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721608 prefixEnd_721608 := by exact prefixLift 721608
  have htrace : WordTrace (prefixWord ++ tailWord_721608) baseStart_721608 baseEnd_721608 := by
    simpa [prefixWord, tailWord_721608, baseEnd_721608] using wordTrace_append hprefix tailTrace_721608
  have hstable : (prefixWord ++ tailWord_721608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721608).length < 2 ^ (prefixWord ++ tailWord_721608).sum := by decide
  have hdescent : baseEnd_721608 < baseStart_721608 := by decide
  rcases family_descends (prefixWord ++ tailWord_721608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721648 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 5]
def baseStart_721648 : Nat := 118140960795 + 721648 * 2 ^ 59
def prefixEnd_721648 : Nat := 4983230072969 + 3 ^ 40 * 721648 * 2
def baseEnd_721648 : Nat := 370552287355897782581207

theorem tailTrace_721648 : CollatzResearch.WordTrace tailWord_721648 prefixEnd_721648 370552287355897782581207 := by
  unfold tailWord_721648
  simp only [CollatzResearch.WordTrace]
  refine ⟨13160332444800009255630799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17547109926400012340841065 13160332444800009255630799)
  ·
    refine ⟨19740498667200013883446199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13160332444800009255630799 19740498667200013883446199)
    ·
      refine ⟨29610748000800020825169299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19740498667200013883446199 29610748000800020825169299)
      ·
        refine ⟨44416122001200031237753949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29610748000800020825169299 44416122001200031237753949)
        ·
          refine ⟨16656045750450011714157731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44416122001200031237753949 16656045750450011714157731)
          ·
            refine ⟨24984068625675017571236597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16656045750450011714157731 24984068625675017571236597)
            ·
              refine ⟨2342256433657032897303431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24984068625675017571236597 2342256433657032897303431)
              ·
                refine ⟨3513384650485549345955147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342256433657032897303431 3513384650485549345955147)
                ·
                  refine ⟨5270076975728324018932721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3513384650485549345955147 5270076975728324018932721)
                  ·
                    refine ⟨3952557731796243014199541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5270076975728324018932721 3952557731796243014199541)
                    ·
                      refine ⟨370552287355897782581207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3952557731796243014199541 370552287355897782581207)
                      ·
                        rfl

theorem cell23_721648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_721648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721648 prefixEnd_721648 := by exact prefixLift 721648
  have htrace : WordTrace (prefixWord ++ tailWord_721648) baseStart_721648 baseEnd_721648 := by
    simpa [prefixWord, tailWord_721648, baseEnd_721648] using wordTrace_append hprefix tailTrace_721648
  have hstable : (prefixWord ++ tailWord_721648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721648).length < 2 ^ (prefixWord ++ tailWord_721648).sum := by decide
  have hdescent : baseEnd_721648 < baseStart_721648 := by decide
  rcases family_descends (prefixWord ++ tailWord_721648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721658 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4]
def baseStart_721658 : Nat := 118140960795 + 721658 * 2 ^ 59
def prefixEnd_721658 : Nat := 4983230072969 + 3 ^ 40 * 721658 * 2
def baseEnd_721658 : Nat := 370557422162442743456161

theorem tailTrace_721658 : CollatzResearch.WordTrace tailWord_721658 prefixEnd_721658 370557422162442743456161 := by
  unfold tailWord_721658
  simp only [CollatzResearch.WordTrace]
  refine ⟨6580257404890947554781407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17547353079709193479417085 6580257404890947554781407)
  ·
    refine ⟨9870386107336421332172111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6580257404890947554781407 9870386107336421332172111)
    ·
      refine ⟨14805579161004631998258167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9870386107336421332172111 14805579161004631998258167)
      ·
        refine ⟨22208368741506947997387251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14805579161004631998258167 22208368741506947997387251)
        ·
          refine ⟨33312553112260421996080877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22208368741506947997387251 33312553112260421996080877)
          ·
            refine ⟨12492207417097658248530329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33312553112260421996080877 12492207417097658248530329)
            ·
              refine ⟨9369155562823243686397747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12492207417097658248530329 9369155562823243686397747)
              ·
                refine ⟨14053733344234865529596621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9369155562823243686397747 14053733344234865529596621)
                ·
                  refine ⟨5270150004088074573598733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14053733344234865529596621 5270150004088074573598733)
                  ·
                    refine ⟨1976306251533027965099525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5270150004088074573598733 1976306251533027965099525)
                    ·
                      refine ⟨370557422162442743456161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1976306251533027965099525 370557422162442743456161)
                      ·
                        rfl

theorem cell23_721658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_721658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721658 prefixEnd_721658 := by exact prefixLift 721658
  have htrace : WordTrace (prefixWord ++ tailWord_721658) baseStart_721658 baseEnd_721658 := by
    simpa [prefixWord, tailWord_721658, baseEnd_721658] using wordTrace_append hprefix tailTrace_721658
  have hstable : (prefixWord ++ tailWord_721658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721658).length < 2 ^ (prefixWord ++ tailWord_721658).sum := by decide
  have hdescent : baseEnd_721658 < baseStart_721658 := by decide
  rcases family_descends (prefixWord ++ tailWord_721658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721675 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 4, 4, 2]
def baseStart_721675 : Nat := 118140960795 + 721675 * 2 ^ 59
def prefixEnd_721675 : Nat := 4983230072969 + 3 ^ 40 * 721675 * 2
def baseEnd_721675 : Nat := 370566151333569176943583

theorem tailTrace_721675 : CollatzResearch.WordTrace tailWord_721675 prefixEnd_721675 370566151333569176943583 := by
  unfold tailWord_721675
  simp only [CollatzResearch.WordTrace]
  refine ⟨26321649660502202122494479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17547766440334801414996319 26321649660502202122494479)
  ·
    refine ⟨39482474490753303183741719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26321649660502202122494479 39482474490753303183741719)
    ·
      refine ⟨59223711736129954775612579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39482474490753303183741719 59223711736129954775612579)
      ·
        refine ⟨88835567604194932163418869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59223711736129954775612579 88835567604194932163418869)
        ·
          refine ⟨8328334462893274890320519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88835567604194932163418869 8328334462893274890320519)
          ·
            refine ⟨12492501694339912335480779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8328334462893274890320519 12492501694339912335480779)
            ·
              refine ⟨18738752541509868503221169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12492501694339912335480779 18738752541509868503221169)
              ·
                refine ⟨14054064406132401377415877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18738752541509868503221169 14054064406132401377415877)
                ·
                  refine ⟨2635137076149825258265477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14054064406132401377415877 2635137076149825258265477)
                  ·
                    refine ⟨494088201778092235924777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2635137076149825258265477 494088201778092235924777)
                    ·
                      refine ⟨370566151333569176943583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 494088201778092235924777 370566151333569176943583)
                      ·
                        rfl

theorem cell23_721675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 4, 2].length) (baseStart_721675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721675 prefixEnd_721675 := by exact prefixLift 721675
  have htrace : WordTrace (prefixWord ++ tailWord_721675) baseStart_721675 baseEnd_721675 := by
    simpa [prefixWord, tailWord_721675, baseEnd_721675] using wordTrace_append hprefix tailTrace_721675
  have hstable : (prefixWord ++ tailWord_721675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721675).length < 2 ^ (prefixWord ++ tailWord_721675).sum := by decide
  have hdescent : baseEnd_721675 < baseStart_721675 := by decide
  rcases family_descends (prefixWord ++ tailWord_721675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721688 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 2, 1, 6]
def baseStart_721688 : Nat := 118140960795 + 721688 * 2 ^ 59
def prefixEnd_721688 : Nat := 4983230072969 + 3 ^ 40 * 721688 * 2
def baseEnd_721688 : Nat := 370572826582077626081023

theorem tailTrace_721688 : CollatzResearch.WordTrace tailWord_721688 prefixEnd_721688 370572826582077626081023 := by
  unfold tailWord_721688
  simp only [CollatzResearch.WordTrace]
  refine ⟨13161061904727552671358859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17548082539636736895145145 13161061904727552671358859)
  ·
    refine ⟨19741592857091329007038289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13161061904727552671358859 19741592857091329007038289)
    ·
      refine ⟨14806194642818496755278717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19741592857091329007038289 14806194642818496755278717)
      ·
        refine ⟨5552322991056936283229519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14806194642818496755278717 5552322991056936283229519)
        ·
          refine ⟨8328484486585404424844279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5552322991056936283229519 8328484486585404424844279)
          ·
            refine ⟨12492726729878106637266419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8328484486585404424844279 12492726729878106637266419)
            ·
              refine ⟨18739090094817159955899629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12492726729878106637266419 18739090094817159955899629)
              ·
                refine ⟨7027158785556434983462361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18739090094817159955899629 7027158785556434983462361)
                ·
                  refine ⟨5270369089167326237596771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7027158785556434983462361 5270369089167326237596771)
                  ·
                    refine ⟨7905553633750989356395157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5270369089167326237596771 7905553633750989356395157)
                    ·
                      refine ⟨370572826582077626081023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7905553633750989356395157 370572826582077626081023)
                      ·
                        rfl

theorem cell23_721688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_721688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721688 prefixEnd_721688 := by exact prefixLift 721688
  have htrace : WordTrace (prefixWord ++ tailWord_721688) baseStart_721688 baseEnd_721688 := by
    simpa [prefixWord, tailWord_721688, baseEnd_721688] using wordTrace_append hprefix tailTrace_721688
  have hstable : (prefixWord ++ tailWord_721688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721688).length < 2 ^ (prefixWord ++ tailWord_721688).sum := by decide
  have hdescent : baseEnd_721688 < baseStart_721688 := by decide
  rcases family_descends (prefixWord ++ tailWord_721688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721693 : List Nat := [1, 4, 2, 4, 2, 1, 2, 2, 5]
def baseStart_721693 : Nat := 118140960795 + 721693 * 2 ^ 59
def prefixEnd_721693 : Nat := 4983230072969 + 3 ^ 40 * 721693 * 2
def baseEnd_721693 : Nat := 41175043776150011835389

theorem tailTrace_721693 : CollatzResearch.WordTrace tailWord_721693 prefixEnd_721693 41175043776150011835389 := by
  unfold tailWord_721693
  simp only [CollatzResearch.WordTrace]
  refine ⟨26322306174436991196649733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17548204116291327464433155 26322306174436991196649733)
  ·
    refine ⟨4935432407706935849371825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26322306174436991196649733 4935432407706935849371825)
    ·
      refine ⟨3701574305780201887028869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4935432407706935849371825 3701574305780201887028869)
      ·
        refine ⟨694045182333787853817913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3701574305780201887028869 694045182333787853817913)
        ·
          refine ⟨520533886750340890363435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 694045182333787853817913 520533886750340890363435)
          ·
            refine ⟨780800830125511335545153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520533886750340890363435 780800830125511335545153)
            ·
              refine ⟨585600622594133501658865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 780800830125511335545153 585600622594133501658865)
              ·
                refine ⟨439200466945600126244149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585600622594133501658865 439200466945600126244149)
                ·
                  refine ⟨41175043776150011835389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 439200466945600126244149 41175043776150011835389)
                  ·
                    rfl

theorem cell23_721693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_721693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721693 prefixEnd_721693 := by exact prefixLift 721693
  have htrace : WordTrace (prefixWord ++ tailWord_721693) baseStart_721693 baseEnd_721693 := by
    simpa [prefixWord, tailWord_721693, baseEnd_721693] using wordTrace_append hprefix tailTrace_721693
  have hstable : (prefixWord ++ tailWord_721693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721693).length < 2 ^ (prefixWord ++ tailWord_721693).sum := by decide
  have hdescent : baseEnd_721693 < baseStart_721693 := by decide
  rcases family_descends (prefixWord ++ tailWord_721693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721715 : List Nat := [1, 1, 1, 2, 6, 1, 2, 3, 6]
def baseStart_721715 : Nat := 118140960795 + 721715 * 2 ^ 59
def prefixEnd_721715 : Nat := 4983230072969 + 3 ^ 40 * 721715 * 2
def baseEnd_721715 : Nat := 41176298951083224493711

theorem tailTrace_721715 : CollatzResearch.WordTrace tailWord_721715 prefixEnd_721715 41176298951083224493711 := by
  unfold tailWord_721715
  simp only [CollatzResearch.WordTrace]
  refine ⟨26323108580357288953950599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17548739053571525969300399 26323108580357288953950599)
  ·
    refine ⟨39484662870535933430925899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26323108580357288953950599 39484662870535933430925899)
    ·
      refine ⟨59226994305803900146388849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39484662870535933430925899 59226994305803900146388849)
      ·
        refine ⟨44420245729352925109791637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59226994305803900146388849 44420245729352925109791637)
        ·
          refine ⟨2082199018563418364521483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44420245729352925109791637 2082199018563418364521483)
          ·
            refine ⟨3123298527845127546782225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082199018563418364521483 3123298527845127546782225)
            ·
              refine ⟨2342473895883845660086669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3123298527845127546782225 2342473895883845660086669)
              ·
                refine ⟨878427710956442122532501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2342473895883845660086669 878427710956442122532501)
                ·
                  refine ⟨41176298951083224493711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 878427710956442122532501 41176298951083224493711)
                  ·
                    rfl

theorem cell23_721715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 6].length) (baseStart_721715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721715 prefixEnd_721715 := by exact prefixLift 721715
  have htrace : WordTrace (prefixWord ++ tailWord_721715) baseStart_721715 baseEnd_721715 := by
    simpa [prefixWord, tailWord_721715, baseEnd_721715] using wordTrace_append hprefix tailTrace_721715
  have hstable : (prefixWord ++ tailWord_721715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721715).length < 2 ^ (prefixWord ++ tailWord_721715).sum := by decide
  have hdescent : baseEnd_721715 < baseStart_721715 := by decide
  rcases family_descends (prefixWord ++ tailWord_721715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721726 : List Nat := [4, 2, 1, 2, 4, 1, 1, 1, 2, 1, 4]
def baseStart_721726 : Nat := 118140960795 + 721726 * 2 ^ 59
def prefixEnd_721726 : Nat := 4983230072969 + 3 ^ 40 * 721726 * 2
def baseEnd_721726 : Nat := 370592338846948477405849

theorem tailTrace_721726 : CollatzResearch.WordTrace tailWord_721726 prefixEnd_721726 370592338846948477405849 := by
  unfold tailWord_721726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3290438722914679729075129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17549006522211625221734021 3290438722914679729075129)
  ·
    refine ⟨2467829042186009796806347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3290438722914679729075129 2467829042186009796806347)
    ·
      refine ⟨3701743563279014695209521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2467829042186009796806347 3701743563279014695209521)
      ·
        refine ⟨2776307672459261021407141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3701743563279014695209521 2776307672459261021407141)
        ·
          refine ⟨520557688586111441513839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2776307672459261021407141 520557688586111441513839)
          ·
            refine ⟨780836532879167162270759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520557688586111441513839 780836532879167162270759)
            ·
              refine ⟨1171254799318750743406139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 780836532879167162270759 1171254799318750743406139)
              ·
                refine ⟨1756882198978126115109209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1171254799318750743406139 1756882198978126115109209)
                ·
                  refine ⟨1317661649233594586331907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1756882198978126115109209 1317661649233594586331907)
                  ·
                    refine ⟨1976492473850391879497861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1317661649233594586331907 1976492473850391879497861)
                    ·
                      refine ⟨370592338846948477405849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1976492473850391879497861 370592338846948477405849)
                      ·
                        rfl

theorem cell23_721726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_721726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721726 prefixEnd_721726 := by exact prefixLift 721726
  have htrace : WordTrace (prefixWord ++ tailWord_721726) baseStart_721726 baseEnd_721726 := by
    simpa [prefixWord, tailWord_721726, baseEnd_721726] using wordTrace_append hprefix tailTrace_721726
  have hstable : (prefixWord ++ tailWord_721726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721726).length < 2 ^ (prefixWord ++ tailWord_721726).sum := by decide
  have hdescent : baseEnd_721726 < baseStart_721726 := by decide
  rcases family_descends (prefixWord ++ tailWord_721726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721729 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_721729 : Nat := 118140960795 + 721729 * 2 ^ 59
def prefixEnd_721729 : Nat := 4983230072969 + 3 ^ 40 * 721729 * 2
def baseEnd_721729 : Nat := 370593879288911965668335

theorem tailTrace_721729 : CollatzResearch.WordTrace tailWord_721729 prefixEnd_721729 370593879288911965668335 := by
  unfold tailWord_721729
  simp only [CollatzResearch.WordTrace]
  refine ⟨26323619202306569344960241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17549079468204379563306827 26323619202306569344960241)
  ·
    refine ⟨19742714401729927008720181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26323619202306569344960241 19742714401729927008720181)
    ·
      refine ⟨1850879475162180657067517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19742714401729927008720181 1850879475162180657067517)
      ·
        refine ⟨694079803185817746400319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1850879475162180657067517 694079803185817746400319)
        ·
          refine ⟨1041119704778726619600479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694079803185817746400319 1041119704778726619600479)
          ·
            refine ⟨1561679557168089929400719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041119704778726619600479 1561679557168089929400719)
            ·
              refine ⟨2342519335752134894101079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561679557168089929400719 2342519335752134894101079)
              ·
                refine ⟨3513779003628202341151619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342519335752134894101079 3513779003628202341151619)
                ·
                  refine ⟨5270668505442303511727429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3513779003628202341151619 5270668505442303511727429)
                  ·
                    refine ⟨988250344770431908448893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5270668505442303511727429 988250344770431908448893)
                    ·
                      refine ⟨370593879288911965668335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 988250344770431908448893 370593879288911965668335)
                      ·
                        rfl

theorem cell23_721729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_721729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721729 prefixEnd_721729 := by exact prefixLift 721729
  have htrace : WordTrace (prefixWord ++ tailWord_721729) baseStart_721729 baseEnd_721729 := by
    simpa [prefixWord, tailWord_721729, baseEnd_721729] using wordTrace_append hprefix tailTrace_721729
  have hstable : (prefixWord ++ tailWord_721729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721729).length < 2 ^ (prefixWord ++ tailWord_721729).sum := by decide
  have hdescent : baseEnd_721729 < baseStart_721729 := by decide
  rcases family_descends (prefixWord ++ tailWord_721729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721752 : List Nat := [2, 1, 2, 2, 1, 1, 1, 6, 2, 3, 2]
def baseStart_721752 : Nat := 118140960795 + 721752 * 2 ^ 59
def prefixEnd_721752 : Nat := 4983230072969 + 3 ^ 40 * 721752 * 2
def baseEnd_721752 : Nat := 370605689343965375680729

theorem tailTrace_721752 : CollatzResearch.WordTrace tailWord_721752 prefixEnd_721752 370605689343965375680729 := by
  unfold tailWord_721752
  simp only [CollatzResearch.WordTrace]
  refine ⟨13162229040611622136523755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17549638720815496182031673 13162229040611622136523755)
  ·
    refine ⟨19743343560917433204785633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13162229040611622136523755 19743343560917433204785633)
    ·
      refine ⟨14807507670688074903589225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19743343560917433204785633 14807507670688074903589225)
      ·
        refine ⟨11105630753016056177691919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14807507670688074903589225 11105630753016056177691919)
        ·
          refine ⟨16658446129524084266537879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11105630753016056177691919 16658446129524084266537879)
          ·
            refine ⟨24987669194286126399806819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16658446129524084266537879 24987669194286126399806819)
            ·
              refine ⟨37481503791429189599710229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24987669194286126399806819 37481503791429189599710229)
              ·
                refine ⟨1756945490223243262486417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37481503791429189599710229 1756945490223243262486417)
                ·
                  refine ⟨1317709117667432446864813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1756945490223243262486417 1317709117667432446864813)
                  ·
                    refine ⟨494140919125287167574305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1317709117667432446864813 494140919125287167574305)
                    ·
                      refine ⟨370605689343965375680729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 494140919125287167574305 370605689343965375680729)
                      ·
                        rfl

theorem cell23_721752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_721752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721752 prefixEnd_721752 := by exact prefixLift 721752
  have htrace : WordTrace (prefixWord ++ tailWord_721752) baseStart_721752 baseEnd_721752 := by
    simpa [prefixWord, tailWord_721752, baseEnd_721752] using wordTrace_append hprefix tailTrace_721752
  have hstable : (prefixWord ++ tailWord_721752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721752).length < 2 ^ (prefixWord ++ tailWord_721752).sum := by decide
  have hdescent : baseEnd_721752 < baseStart_721752 := by decide
  rcases family_descends (prefixWord ++ tailWord_721752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721759 : List Nat := [1, 1, 2, 3, 1, 3, 1, 6, 1, 1, 3]
def baseStart_721759 : Nat := 118140960795 + 721759 * 2 ^ 59
def prefixEnd_721759 : Nat := 4983230072969 + 3 ^ 40 * 721759 * 2
def baseEnd_721759 : Nat := 370609283708546848293197

theorem tailTrace_721759 : CollatzResearch.WordTrace tailWord_721759 prefixEnd_721759 370609283708546848293197 := by
  unfold tailWord_721759
  simp only [CollatzResearch.WordTrace]
  refine ⟨26324713392197884468552331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17549808928131922979034887 26324713392197884468552331)
  ·
    refine ⟨39487070088296826702828497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26324713392197884468552331 39487070088296826702828497)
    ·
      refine ⟨29615302566222620027121373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39487070088296826702828497 29615302566222620027121373)
      ·
        refine ⟨11105738462333482510170515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29615302566222620027121373 11105738462333482510170515)
        ·
          refine ⟨16658607693500223765255773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11105738462333482510170515 16658607693500223765255773)
          ·
            refine ⟨6246977885062583911970915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16658607693500223765255773 6246977885062583911970915)
            ·
              refine ⟨9370466827593875867956373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6246977885062583911970915 9370466827593875867956373)
              ·
                refine ⟨439240632543462931310455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9370466827593875867956373 439240632543462931310455)
                ·
                  refine ⟨658860948815194396965683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439240632543462931310455 658860948815194396965683)
                  ·
                    refine ⟨988291423222791595448525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 658860948815194396965683 988291423222791595448525)
                    ·
                      refine ⟨370609283708546848293197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 988291423222791595448525 370609283708546848293197)
                      ·
                        rfl

theorem cell23_721759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 1, 1, 3].length) (baseStart_721759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721759 prefixEnd_721759 := by exact prefixLift 721759
  have htrace : WordTrace (prefixWord ++ tailWord_721759) baseStart_721759 baseEnd_721759 := by
    simpa [prefixWord, tailWord_721759, baseEnd_721759] using wordTrace_append hprefix tailTrace_721759
  have hstable : (prefixWord ++ tailWord_721759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721759).length < 2 ^ (prefixWord ++ tailWord_721759).sum := by decide
  have hdescent : baseEnd_721759 < baseStart_721759 := by decide
  rcases family_descends (prefixWord ++ tailWord_721759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721765 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 5, 1, 4]
def baseStart_721765 : Nat := 118140960795 + 721765 * 2 ^ 59
def prefixEnd_721765 : Nat := 4983230072969 + 3 ^ 40 * 721765 * 2
def baseEnd_721765 : Nat := 370612364592473824818169

theorem tailTrace_721765 : CollatzResearch.WordTrace tailWord_721765 prefixEnd_721765 370612364592473824818169 := by
  unfold tailWord_721765
  simp only [CollatzResearch.WordTrace]
  refine ⟨26324932230176147493270749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17549954820117431662180499 26324932230176147493270749)
  ·
    refine ⟨9871849586316055309976531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26324932230176147493270749 9871849586316055309976531)
    ·
      refine ⟨14807774379474082964964797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9871849586316055309976531 14807774379474082964964797)
      ·
        refine ⟨5552915392302781111861799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14807774379474082964964797 5552915392302781111861799)
        ·
          refine ⟨8329373088454171667792699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5552915392302781111861799 8329373088454171667792699)
          ·
            refine ⟨12494059632681257501689049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8329373088454171667792699 12494059632681257501689049)
            ·
              refine ⟨9370544724510943126266787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12494059632681257501689049 9370544724510943126266787)
              ·
                refine ⟨14055817086766414689400181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9370544724510943126266787 14055817086766414689400181)
                ·
                  refine ⟨1317732851884351377131267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14055817086766414689400181 1317732851884351377131267)
                  ·
                    refine ⟨1976599277826527065696901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1317732851884351377131267 1976599277826527065696901)
                    ·
                      refine ⟨370612364592473824818169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1976599277826527065696901 370612364592473824818169)
                      ·
                        rfl

theorem cell23_721765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_721765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721765 prefixEnd_721765 := by exact prefixLift 721765
  have htrace : WordTrace (prefixWord ++ tailWord_721765) baseStart_721765 baseEnd_721765 := by
    simpa [prefixWord, tailWord_721765, baseEnd_721765] using wordTrace_append hprefix tailTrace_721765
  have hstable : (prefixWord ++ tailWord_721765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721765).length < 2 ^ (prefixWord ++ tailWord_721765).sum := by decide
  have hdescent : baseEnd_721765 < baseStart_721765 := by decide
  rcases family_descends (prefixWord ++ tailWord_721765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721795 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 4]
def baseStart_721795 : Nat := 118140960795 + 721795 * 2 ^ 59
def prefixEnd_721795 : Nat := 4983230072969 + 3 ^ 40 * 721795 * 2
def baseEnd_721795 : Nat := 370627769012108707443031

theorem tailTrace_721795 : CollatzResearch.WordTrace tailWord_721795 prefixEnd_721795 370627769012108707443031 := by
  unfold tailWord_721795
  simp only [CollatzResearch.WordTrace]
  refine ⟨26326026420067462616862839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17550684280044975077908559 26326026420067462616862839)
  ·
    refine ⟨39489039630101193925294259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26326026420067462616862839 39489039630101193925294259)
    ·
      refine ⟨59233559445151790887941389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39489039630101193925294259 59233559445151790887941389)
      ·
        refine ⟨22212584791931921582978021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59233559445151790887941389 22212584791931921582978021)
        ·
          refine ⟨4164859648487235296808379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22212584791931921582978021 4164859648487235296808379)
          ·
            refine ⟨6247289472730852945212569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4164859648487235296808379 6247289472730852945212569)
            ·
              refine ⟨4685467104548139708909427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6247289472730852945212569 4685467104548139708909427)
              ·
                refine ⟨7028200656822209563364141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4685467104548139708909427 7028200656822209563364141)
                ·
                  refine ⟨2635575246308328586261553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7028200656822209563364141 2635575246308328586261553)
                  ·
                    refine ⟨1976681434731246439696165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2635575246308328586261553 1976681434731246439696165)
                    ·
                      refine ⟨370627769012108707443031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1976681434731246439696165 370627769012108707443031)
                      ·
                        rfl

theorem cell23_721795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_721795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721795 prefixEnd_721795 := by exact prefixLift 721795
  have htrace : WordTrace (prefixWord ++ tailWord_721795) baseStart_721795 baseEnd_721795 := by
    simpa [prefixWord, tailWord_721795, baseEnd_721795] using wordTrace_append hprefix tailTrace_721795
  have hstable : (prefixWord ++ tailWord_721795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721795).length < 2 ^ (prefixWord ++ tailWord_721795).sum := by decide
  have hdescent : baseEnd_721795 < baseStart_721795 := by decide
  rcases family_descends (prefixWord ++ tailWord_721795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721802 : List Nat := [3, 1, 2, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_721802 : Nat := 118140960795 + 721802 * 2 ^ 59
def prefixEnd_721802 : Nat := 4983230072969 + 3 ^ 40 * 721802 * 2
def baseEnd_721802 : Nat := 370631363376690180055499

theorem tailTrace_721802 : CollatzResearch.WordTrace tailWord_721802 prefixEnd_721802 370631363376690180055499 := by
  unfold tailWord_721802
  simp only [CollatzResearch.WordTrace]
  refine ⟨6581570432760525703091915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17550854487361401874911773 6581570432760525703091915)
  ·
    refine ⟨9872355649140788554637873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6581570432760525703091915 9872355649140788554637873)
    ·
      refine ⟨7404266736855591415978405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9872355649140788554637873 7404266736855591415978405)
      ·
        refine ⟨1388300013160423390495951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7404266736855591415978405 1388300013160423390495951)
        ·
          refine ⟨2082450019740635085743927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1388300013160423390495951 2082450019740635085743927)
          ·
            refine ⟨3123675029610952628615891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082450019740635085743927 3123675029610952628615891)
            ·
              refine ⟨4685512544416428942923837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3123675029610952628615891 4685512544416428942923837)
              ·
                refine ⟨1757067204156160853596439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4685512544416428942923837 1757067204156160853596439)
                ·
                  refine ⟨2635600806234241280394659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1757067204156160853596439 2635600806234241280394659)
                  ·
                    refine ⟨3953401209351361920591989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2635600806234241280394659 3953401209351361920591989)
                    ·
                      refine ⟨370631363376690180055499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3953401209351361920591989 370631363376690180055499)
                      ·
                        rfl

theorem cell23_721802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_721802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721802 prefixEnd_721802 := by exact prefixLift 721802
  have htrace : WordTrace (prefixWord ++ tailWord_721802) baseStart_721802 baseEnd_721802 := by
    simpa [prefixWord, tailWord_721802, baseEnd_721802] using wordTrace_append hprefix tailTrace_721802
  have hstable : (prefixWord ++ tailWord_721802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721802).length < 2 ^ (prefixWord ++ tailWord_721802).sum := by decide
  have hdescent : baseEnd_721802 < baseStart_721802 := by decide
  rcases family_descends (prefixWord ++ tailWord_721802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721810 : List Nat := [3, 2, 3, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_721810 : Nat := 118140960795 + 721810 * 2 ^ 59
def prefixEnd_721810 : Nat := 4983230072969 + 3 ^ 40 * 721810 * 2
def baseEnd_721810 : Nat := 370635471221926148755463

theorem tailTrace_721810 : CollatzResearch.WordTrace tailWord_721810 prefixEnd_721810 370635471221926148755463 := by
  unfold tailWord_721810
  simp only [CollatzResearch.WordTrace]
  refine ⟨6581643378753280044664721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17551049010008746785772589 6581643378753280044664721)
  ·
    refine ⟨4936232534064960033498541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6581643378753280044664721 4936232534064960033498541)
    ·
      refine ⟨1851087200274360012561953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4936232534064960033498541 1851087200274360012561953)
      ·
        refine ⟨1388315400205770009421465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1851087200274360012561953 1388315400205770009421465)
        ·
          refine ⟨1041236550154327507066099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1388315400205770009421465 1041236550154327507066099)
          ·
            refine ⟨1561854825231491260599149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041236550154327507066099 1561854825231491260599149)
            ·
              refine ⟨585695559461809222724681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1561854825231491260599149 585695559461809222724681)
              ·
                refine ⟨439271669596356917043511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585695559461809222724681 439271669596356917043511)
                ·
                  refine ⟨658907504394535375565267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439271669596356917043511 658907504394535375565267)
                  ·
                    refine ⟨988361256591803063347901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 658907504394535375565267 988361256591803063347901)
                    ·
                      refine ⟨370635471221926148755463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 988361256591803063347901 370635471221926148755463)
                      ·
                        rfl

theorem cell23_721810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_721810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721810 prefixEnd_721810 := by exact prefixLift 721810
  have htrace : WordTrace (prefixWord ++ tailWord_721810) baseStart_721810 baseEnd_721810 := by
    simpa [prefixWord, tailWord_721810, baseEnd_721810] using wordTrace_append hprefix tailTrace_721810
  have hstable : (prefixWord ++ tailWord_721810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721810).length < 2 ^ (prefixWord ++ tailWord_721810).sum := by decide
  have hdescent : baseEnd_721810 < baseStart_721810 := by decide
  rcases family_descends (prefixWord ++ tailWord_721810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721826 : List Nat := [3, 3, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_721826 : Nat := 118140960795 + 721826 * 2 ^ 59
def prefixEnd_721826 : Nat := 4983230072969 + 3 ^ 40 * 721826 * 2
def baseEnd_721826 : Nat := 123547895637466028718463

theorem tailTrace_721826 : CollatzResearch.WordTrace tailWord_721826 prefixEnd_721826 123547895637466028718463 := by
  unfold tailWord_721826
  simp only [CollatzResearch.WordTrace]
  refine ⟨6581789270738788727810333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17551438055303436607494221 6581789270738788727810333)
  ·
    refine ⟨2468170976527045772928875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6581789270738788727810333 2468170976527045772928875)
    ·
      refine ⟨3702256464790568659393313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2468170976527045772928875 3702256464790568659393313)
      ·
        refine ⟨2776692348592926494544985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3702256464790568659393313 2776692348592926494544985)
        ·
          refine ⟨2082519261444694870908739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2776692348592926494544985 2082519261444694870908739)
          ·
            refine ⟨3123778892167042306363109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082519261444694870908739 3123778892167042306363109)
            ·
              refine ⟨585708542281320432443083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3123778892167042306363109 585708542281320432443083)
              ·
                refine ⟨878562813421980648664625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585708542281320432443083 878562813421980648664625)
                ·
                  refine ⟨658922110066485486498469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 878562813421980648664625 658922110066485486498469)
                  ·
                    refine ⟨123547895637466028718463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 658922110066485486498469 123547895637466028718463)
                    ·
                      rfl

theorem cell23_721826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_721826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721826 prefixEnd_721826 := by exact prefixLift 721826
  have htrace : WordTrace (prefixWord ++ tailWord_721826) baseStart_721826 baseEnd_721826 := by
    simpa [prefixWord, tailWord_721826, baseEnd_721826] using wordTrace_append hprefix tailTrace_721826
  have hstable : (prefixWord ++ tailWord_721826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721826).length < 2 ^ (prefixWord ++ tailWord_721826).sum := by decide
  have hdescent : baseEnd_721826 < baseStart_721826 := by decide
  rcases family_descends (prefixWord ++ tailWord_721826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721872 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 5, 4, 2]
def baseStart_721872 : Nat := 118140960795 + 721872 * 2 ^ 59
def prefixEnd_721872 : Nat := 4983230072969 + 3 ^ 40 * 721872 * 2
def baseEnd_721872 : Nat := 370667307022504906180177

theorem tailTrace_721872 : CollatzResearch.WordTrace tailWord_721872 prefixEnd_721872 370667307022504906180177 := by
  unfold tailWord_721872
  simp only [CollatzResearch.WordTrace]
  refine ⟨13164417420394252383707935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17552556560525669844943913 13164417420394252383707935)
  ·
    refine ⟨19746626130591378575561903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13164417420394252383707935 19746626130591378575561903)
    ·
      refine ⟨29619939195887067863342855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19746626130591378575561903 29619939195887067863342855)
      ·
        refine ⟨44429908793830601795014283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29619939195887067863342855 44429908793830601795014283)
        ·
          refine ⟨66644863190745902692521425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44429908793830601795014283 66644863190745902692521425)
          ·
            refine ⟨49983647393059427019391069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66644863190745902692521425 49983647393059427019391069)
            ·
              refine ⟨18743867772397285132271651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49983647393059427019391069 18743867772397285132271651)
              ·
                refine ⟨28115801658595927698407477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18743867772397285132271651 28115801658595927698407477)
                ·
                  refine ⟨2635856405493368221725701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28115801658595927698407477 2635856405493368221725701)
                  ·
                    refine ⟨494223076030006541573569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2635856405493368221725701 494223076030006541573569)
                    ·
                      refine ⟨370667307022504906180177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 494223076030006541573569 370667307022504906180177)
                      ·
                        rfl

theorem cell23_721872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 5, 4, 2].length) (baseStart_721872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721872 prefixEnd_721872 := by exact prefixLift 721872
  have htrace : WordTrace (prefixWord ++ tailWord_721872) baseStart_721872 baseEnd_721872 := by
    simpa [prefixWord, tailWord_721872, baseEnd_721872] using wordTrace_append hprefix tailTrace_721872
  have hstable : (prefixWord ++ tailWord_721872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721872).length < 2 ^ (prefixWord ++ tailWord_721872).sum := by decide
  have hdescent : baseEnd_721872 < baseStart_721872 := by decide
  rcases family_descends (prefixWord ++ tailWord_721872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721882 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 2, 6]
def baseStart_721882 : Nat := 118140960795 + 721882 * 2 ^ 59
def prefixEnd_721882 : Nat := 4983230072969 + 3 ^ 40 * 721882 * 2
def baseEnd_721882 : Nat := 123557480609683289018377

theorem tailTrace_721882 : CollatzResearch.WordTrace tailWord_721882 prefixEnd_721882 123557480609683289018377 := by
  unfold tailWord_721882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6582299892688069118819975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17552799713834850983519933 6582299892688069118819975)
  ·
    refine ⟨9873449839032103678229963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6582299892688069118819975 9873449839032103678229963)
    ·
      refine ⟨14810174758548155517344945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9873449839032103678229963 14810174758548155517344945)
      ·
        refine ⟨11107631068911116638008709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14810174758548155517344945 11107631068911116638008709)
        ·
          refine ⟨2082680825420834369626633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11107631068911116638008709 2082680825420834369626633)
          ·
            refine ⟨1562010619065625777219975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2082680825420834369626633 1562010619065625777219975)
            ·
              refine ⟨2343015928598438665829963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1562010619065625777219975 2343015928598438665829963)
              ·
                refine ⟨3514523892897657998744945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2343015928598438665829963 3514523892897657998744945)
                ·
                  refine ⟨2635892919673243499058709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3514523892897657998744945 2635892919673243499058709)
                  ·
                    refine ⟨123557480609683289018377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2635892919673243499058709 123557480609683289018377)
                    ·
                      rfl

theorem cell23_721882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_721882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721882 prefixEnd_721882 := by exact prefixLift 721882
  have htrace : WordTrace (prefixWord ++ tailWord_721882) baseStart_721882 baseEnd_721882 := by
    simpa [prefixWord, tailWord_721882, baseEnd_721882] using wordTrace_append hprefix tailTrace_721882
  have hstable : (prefixWord ++ tailWord_721882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721882).length < 2 ^ (prefixWord ++ tailWord_721882).sum := by decide
  have hdescent : baseEnd_721882 < baseStart_721882 := by decide
  rcases family_descends (prefixWord ++ tailWord_721882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721889 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 6, 2, 2]
def baseStart_721889 : Nat := 118140960795 + 721889 * 2 ^ 59
def prefixEnd_721889 : Nat := 4983230072969 + 3 ^ 40 * 721889 * 2
def baseEnd_721889 : Nat := 370676036193631339667599

theorem tailTrace_721889 : CollatzResearch.WordTrace tailWord_721889 prefixEnd_721889 370676036193631339667599 := by
  unfold tailWord_721889
  simp only [CollatzResearch.WordTrace]
  refine ⟨26329454881726916670784721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17552969921151277780523147 26329454881726916670784721)
  ·
    refine ⟨19747091161295187503088541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26329454881726916670784721 19747091161295187503088541)
    ·
      refine ⟨7405159185485695313658203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19747091161295187503088541 7405159185485695313658203)
      ·
        refine ⟨11107738778228542970487305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7405159185485695313658203 11107738778228542970487305)
        ·
          refine ⟨8330804083671407227865479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11107738778228542970487305 8330804083671407227865479)
          ·
            refine ⟨12496206125507110841798219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8330804083671407227865479 12496206125507110841798219)
            ·
              refine ⟨18744309188260666262697329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12496206125507110841798219 18744309188260666262697329)
              ·
                refine ⟨14058231891195499697022997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18744309188260666262697329 14058231891195499697022997)
                ·
                  refine ⟨658979619899789048297953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14058231891195499697022997 658979619899789048297953)
                  ·
                    refine ⟨494234714924841786223465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 658979619899789048297953 494234714924841786223465)
                    ·
                      refine ⟨370676036193631339667599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 494234714924841786223465 370676036193631339667599)
                      ·
                        rfl

theorem cell23_721889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_721889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721889 prefixEnd_721889 := by exact prefixLift 721889
  have htrace : WordTrace (prefixWord ++ tailWord_721889) baseStart_721889 baseEnd_721889 := by
    simpa [prefixWord, tailWord_721889, baseEnd_721889] using wordTrace_append hprefix tailTrace_721889
  have hstable : (prefixWord ++ tailWord_721889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721889).length < 2 ^ (prefixWord ++ tailWord_721889).sum := by decide
  have hdescent : baseEnd_721889 < baseStart_721889 := by decide
  rcases family_descends (prefixWord ++ tailWord_721889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721910 : List Nat := [5, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2]
def baseStart_721910 : Nat := 118140960795 + 721910 * 2 ^ 59
def prefixEnd_721910 : Nat := 4983230072969 + 3 ^ 40 * 721910 * 2
def baseEnd_721910 : Nat := 370686819287375757505003

theorem tailTrace_721910 : CollatzResearch.WordTrace tailWord_721910 prefixEnd_721910 370686819287375757505003 := by
  unfold tailWord_721910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1645638800915677328581199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17553480543100558171532789 1645638800915677328581199)
  ·
    refine ⟨2468458201373515992871799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1645638800915677328581199 2468458201373515992871799)
    ·
      refine ⟨3702687302060273989307699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2468458201373515992871799 3702687302060273989307699)
      ·
        refine ⟨5554030953090410983961549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3702687302060273989307699 5554030953090410983961549)
        ·
          refine ⟨2082761607408904118985581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5554030953090410983961549 2082761607408904118985581)
          ·
            refine ⟨781035602778339044619593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2082761607408904118985581 781035602778339044619593)
            ·
              refine ⟨585776702083754283464695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 781035602778339044619593 585776702083754283464695)
              ·
                refine ⟨878665053125631425197043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585776702083754283464695 878665053125631425197043)
                ·
                  refine ⟨1317997579688447137795565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 878665053125631425197043 1317997579688447137795565)
                  ·
                    refine ⟨494249092383167676673337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1317997579688447137795565 494249092383167676673337)
                    ·
                      refine ⟨370686819287375757505003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 494249092383167676673337 370686819287375757505003)
                      ·
                        rfl

theorem cell23_721910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_721910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721910 prefixEnd_721910 := by exact prefixLift 721910
  have htrace : WordTrace (prefixWord ++ tailWord_721910) baseStart_721910 baseEnd_721910 := by
    simpa [prefixWord, tailWord_721910, baseEnd_721910] using wordTrace_append hprefix tailTrace_721910
  have hstable : (prefixWord ++ tailWord_721910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721910).length < 2 ^ (prefixWord ++ tailWord_721910).sum := by decide
  have hdescent : baseEnd_721910 < baseStart_721910 := by decide
  rcases family_descends (prefixWord ++ tailWord_721910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721959 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 1, 7]
def baseStart_721959 : Nat := 118140960795 + 721959 * 2 ^ 59
def prefixEnd_721959 : Nat := 4983230072969 + 3 ^ 40 * 721959 * 2
def baseEnd_721959 : Nat := 123570659946482021930759

theorem tailTrace_721959 : CollatzResearch.WordTrace tailWord_721959 prefixEnd_721959 123570659946482021930759 := by
  unfold tailWord_721959
  simp only [CollatzResearch.WordTrace]
  refine ⟨26332007991473318625832931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17554671994315545750555287 26332007991473318625832931)
  ·
    refine ⟨39498011987209977938749397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26332007991473318625832931 39498011987209977938749397)
    ·
      refine ⟨925734655950233857939439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 39498011987209977938749397 925734655950233857939439)
      ·
        refine ⟨1388601983925350786909159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 925734655950233857939439 1388601983925350786909159)
        ·
          refine ⟨2082902975888026180363739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1388601983925350786909159 2082902975888026180363739)
          ·
            refine ⟨3124354463832039270545609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082902975888026180363739 3124354463832039270545609)
            ·
              refine ⟨2343265847874029452909207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3124354463832039270545609 2343265847874029452909207)
              ·
                refine ⟨3514898771811044179363811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2343265847874029452909207 3514898771811044179363811)
                ·
                  refine ⟨5272348157716566269045717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514898771811044179363811 5272348157716566269045717)
                  ·
                    refine ⟨123570659946482021930759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5272348157716566269045717 123570659946482021930759)
                    ·
                      rfl

theorem cell23_721959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_721959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721959 prefixEnd_721959 := by exact prefixLift 721959
  have htrace : WordTrace (prefixWord ++ tailWord_721959) baseStart_721959 baseEnd_721959 := by
    simpa [prefixWord, tailWord_721959, baseEnd_721959] using wordTrace_append hprefix tailTrace_721959
  have hstable : (prefixWord ++ tailWord_721959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721959).length < 2 ^ (prefixWord ++ tailWord_721959).sum := by decide
  have hdescent : baseEnd_721959 < baseStart_721959 := by decide
  rcases family_descends (prefixWord ++ tailWord_721959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721989 : List Nat := [1, 3, 1, 1, 1, 3, 5, 1, 3, 4]
def baseStart_721989 : Nat := 118140960795 + 721989 * 2 ^ 59
def prefixEnd_721989 : Nat := 4983230072969 + 3 ^ 40 * 721989 * 2
def baseEnd_721989 : Nat := 123575794753026982805713

theorem tailTrace_721989 : CollatzResearch.WordTrace tailWord_721989 prefixEnd_721989 123575794753026982805713 := by
  unfold tailWord_721989
  simp only [CollatzResearch.WordTrace]
  refine ⟨26333102181364633749425021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17555401454243089166283347 26333102181364633749425021)
  ·
    refine ⟨9874913318011737656034383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26333102181364633749425021 9874913318011737656034383)
    ·
      refine ⟨14812369977017606484051575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9874913318011737656034383 14812369977017606484051575)
      ·
        refine ⟨22218554965526409726077363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14812369977017606484051575 22218554965526409726077363)
        ·
          refine ⟨33327832448289614589116045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22218554965526409726077363 33327832448289614589116045)
          ·
            refine ⟨12497937168108605470918517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33327832448289614589116045 12497937168108605470918517)
            ·
              refine ⟨1171681609510181762898611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12497937168108605470918517 1171681609510181762898611)
              ·
                refine ⟨1757522414265272644347917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1171681609510181762898611 1757522414265272644347917)
                ·
                  refine ⟨659070905349477241630469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1757522414265272644347917 659070905349477241630469)
                  ·
                    refine ⟨123575794753026982805713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 659070905349477241630469 123575794753026982805713)
                    ·
                      rfl

theorem cell23_721989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_721989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_721989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_721989 prefixEnd_721989 := by exact prefixLift 721989
  have htrace : WordTrace (prefixWord ++ tailWord_721989) baseStart_721989 baseEnd_721989 := by
    simpa [prefixWord, tailWord_721989, baseEnd_721989] using wordTrace_append hprefix tailTrace_721989
  have hstable : (prefixWord ++ tailWord_721989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721989).length < 2 ^ (prefixWord ++ tailWord_721989).sum := by decide
  have hdescent : baseEnd_721989 < baseStart_721989 := by decide
  rcases family_descends (prefixWord ++ tailWord_721989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722013 : List Nat := [1, 4, 4, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_722013 : Nat := 118140960795 + 722013 * 2 ^ 59
def prefixEnd_722013 : Nat := 4983230072969 + 3 ^ 40 * 722013 * 2
def baseEnd_722013 : Nat := 370739707794788854517029

theorem tailTrace_722013 : CollatzResearch.WordTrace tailWord_722013 prefixEnd_722013 370739707794788854517029 := by
  unfold tailWord_722013
  simp only [CollatzResearch.WordTrace]
  refine ⟨26333977533277685848298693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17555985022185123898865795 26333977533277685848298693)
  ·
    refine ⟨4937620787489566096556005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26333977533277685848298693 4937620787489566096556005)
    ·
      refine ⟨925803897654293643104251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4937620787489566096556005 925803897654293643104251)
      ·
        refine ⟨1388705846481440464656377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 925803897654293643104251 1388705846481440464656377)
        ·
          refine ⟨1041529384861080348492283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1388705846481440464656377 1041529384861080348492283)
          ·
            refine ⟨1562294077291620522738425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041529384861080348492283 1562294077291620522738425)
            ·
              refine ⟨1171720557968715392053819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1562294077291620522738425 1171720557968715392053819)
              ·
                refine ⟨1757580836953073088080729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1171720557968715392053819 1757580836953073088080729)
                ·
                  refine ⟨1318185627714804816060547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1757580836953073088080729 1318185627714804816060547)
                  ·
                    refine ⟨1977278441572207224090821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1318185627714804816060547 1977278441572207224090821)
                    ·
                      refine ⟨370739707794788854517029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1977278441572207224090821 370739707794788854517029)
                      ·
                        rfl

theorem cell23_722013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_722013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722013 prefixEnd_722013 := by exact prefixLift 722013
  have htrace : WordTrace (prefixWord ++ tailWord_722013) baseStart_722013 baseEnd_722013 := by
    simpa [prefixWord, tailWord_722013, baseEnd_722013] using wordTrace_append hprefix tailTrace_722013
  have hstable : (prefixWord ++ tailWord_722013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722013).length < 2 ^ (prefixWord ++ tailWord_722013).sum := by decide
  have hdescent : baseEnd_722013 < baseStart_722013 := by decide
  rcases family_descends (prefixWord ++ tailWord_722013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722049 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 3, 5]
def baseStart_722049 : Nat := 118140960795 + 722049 * 2 ^ 59
def prefixEnd_722049 : Nat := 4983230072969 + 3 ^ 40 * 722049 * 2
def baseEnd_722049 : Nat := 123586064366116904555621

theorem tailTrace_722049 : CollatzResearch.WordTrace tailWord_722049 prefixEnd_722049 123586064366116904555621 := by
  unfold tailWord_722049
  simp only [CollatzResearch.WordTrace]
  refine ⟨26335290561147263996609201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17556860374098175997739467 26335290561147263996609201)
  ·
    refine ⟨19751467920860447997456901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26335290561147263996609201 19751467920860447997456901)
    ·
      refine ⟨3703400235161333999523169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19751467920860447997456901 3703400235161333999523169)
      ·
        refine ⟨2777550176371000499642377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3703400235161333999523169 2777550176371000499642377)
        ·
          refine ⟨2083162632278250374731783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2777550176371000499642377 2083162632278250374731783)
          ·
            refine ⟨3124743948417375562097675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2083162632278250374731783 3124743948417375562097675)
            ·
              refine ⟨4687115922626063343146513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3124743948417375562097675 4687115922626063343146513)
              ·
                refine ⟨3515336941969547507359885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4687115922626063343146513 3515336941969547507359885)
                ·
                  refine ⟨1318251353238580315259957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3515336941969547507359885 1318251353238580315259957)
                  ·
                    refine ⟨123586064366116904555621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1318251353238580315259957 123586064366116904555621)
                    ·
                      rfl

theorem cell23_722049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_722049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722049 prefixEnd_722049 := by exact prefixLift 722049
  have htrace : WordTrace (prefixWord ++ tailWord_722049) baseStart_722049 baseEnd_722049 := by
    simpa [prefixWord, tailWord_722049, baseEnd_722049] using wordTrace_append hprefix tailTrace_722049
  have hstable : (prefixWord ++ tailWord_722049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722049).length < 2 ^ (prefixWord ++ tailWord_722049).sum := by decide
  have hdescent : baseEnd_722049 < baseStart_722049 := by decide
  rcases family_descends (prefixWord ++ tailWord_722049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722069 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 1, 8, 2]
def baseStart_722069 : Nat := 118140960795 + 722069 * 2 ^ 59
def prefixEnd_722069 : Nat := 4983230072969 + 3 ^ 40 * 722069 * 2
def baseEnd_722069 : Nat := 370768462711440635416771

theorem tailTrace_722069 : CollatzResearch.WordTrace tailWord_722069 prefixEnd_722069 370768462711440635416771 := by
  unfold tailWord_722069
  simp only [CollatzResearch.WordTrace]
  refine ⟨26336020021074807412337261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17557346680716538274891507 26336020021074807412337261)
  ·
    refine ⟨9876007507903052779626473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26336020021074807412337261 9876007507903052779626473)
    ·
      refine ⟨7407005630927289584719855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9876007507903052779626473 7407005630927289584719855)
      ·
        refine ⟨11110508446390934377079783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7407005630927289584719855 11110508446390934377079783)
        ·
          refine ⟨16665762669586401565619675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11110508446390934377079783 16665762669586401565619675)
          ·
            refine ⟨24998644004379602348429513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16665762669586401565619675 24998644004379602348429513)
            ·
              refine ⟨18748983003284701761322135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24998644004379602348429513 18748983003284701761322135)
              ·
                refine ⟨28123474504927052641983203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18748983003284701761322135 28123474504927052641983203)
                ·
                  refine ⟨42185211757390578962974805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28123474504927052641983203 42185211757390578962974805)
                  ·
                    refine ⟨494357950281920847222361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42185211757390578962974805 494357950281920847222361)
                    ·
                      refine ⟨370768462711440635416771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 494357950281920847222361 370768462711440635416771)
                      ·
                        rfl

theorem cell23_722069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_722069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722069 prefixEnd_722069 := by exact prefixLift 722069
  have htrace : WordTrace (prefixWord ++ tailWord_722069) baseStart_722069 baseEnd_722069 := by
    simpa [prefixWord, tailWord_722069, baseEnd_722069] using wordTrace_append hprefix tailTrace_722069
  have hstable : (prefixWord ++ tailWord_722069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722069).length < 2 ^ (prefixWord ++ tailWord_722069).sum := by decide
  have hdescent : baseEnd_722069 < baseStart_722069 := by decide
  rcases family_descends (prefixWord ++ tailWord_722069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722103 : List Nat := [1, 1, 3, 1, 4, 1, 4, 1, 3, 2, 2]
def baseStart_722103 : Nat := 118140960795 + 722103 * 2 ^ 59
def prefixEnd_722103 : Nat := 4983230072969 + 3 ^ 40 * 722103 * 2
def baseEnd_722103 : Nat := 370785921053693502391615

theorem tailTrace_722103 : CollatzResearch.WordTrace tailWord_722103 prefixEnd_722103 370785921053693502391615 := by
  unfold tailWord_722103
  simp only [CollatzResearch.WordTrace]
  refine ⟨26337260102951631219074963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17558173401967754146049975 26337260102951631219074963)
  ·
    refine ⟨39505890154427446828612445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26337260102951631219074963 39505890154427446828612445)
    ·
      refine ⟨14814708807910292560729667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39505890154427446828612445 14814708807910292560729667)
      ·
        refine ⟨22222063211865438841094501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14814708807910292560729667 22222063211865438841094501)
        ·
          refine ⟨4166636852224769782705219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22222063211865438841094501 4166636852224769782705219)
          ·
            refine ⟨6249955278337154674057829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4166636852224769782705219 6249955278337154674057829)
            ·
              refine ⟨1171866614688216501385843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6249955278337154674057829 1171866614688216501385843)
              ·
                refine ⟨1757799922032324752078765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1171866614688216501385843 1757799922032324752078765)
                ·
                  refine ⟨659174970762121782029537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1757799922032324752078765 659174970762121782029537)
                  ·
                    refine ⟨494381228071591336522153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 659174970762121782029537 494381228071591336522153)
                    ·
                      refine ⟨370785921053693502391615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 494381228071591336522153 370785921053693502391615)
                      ·
                        rfl

theorem cell23_722103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 2, 2].length) (baseStart_722103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722103 prefixEnd_722103 := by exact prefixLift 722103
  have htrace : WordTrace (prefixWord ++ tailWord_722103) baseStart_722103 baseEnd_722103 := by
    simpa [prefixWord, tailWord_722103, baseEnd_722103] using wordTrace_append hprefix tailTrace_722103
  have hstable : (prefixWord ++ tailWord_722103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722103).length < 2 ^ (prefixWord ++ tailWord_722103).sum := by decide
  have hdescent : baseEnd_722103 < baseStart_722103 := by decide
  rcases family_descends (prefixWord ++ tailWord_722103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722113 : List Nat := [1, 2, 6, 1, 1, 3, 1, 1, 1, 6]
def baseStart_722113 : Nat := 118140960795 + 722113 * 2 ^ 59
def prefixEnd_722113 : Nat := 4983230072969 + 3 ^ 40 * 722113 * 2
def baseEnd_722113 : Nat := 123597018620079487755523

theorem tailTrace_722113 : CollatzResearch.WordTrace tailWord_722113 prefixEnd_722113 123597018620079487755523 := by
  unfold tailWord_722113
  simp only [CollatzResearch.WordTrace]
  refine ⟨26337624832915402926938993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17558416555276935284625995 26337624832915402926938993)
  ·
    refine ⟨19753218624686552195204245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26337624832915402926938993 19753218624686552195204245)
    ·
      refine ⟨925932123032182134150199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19753218624686552195204245 925932123032182134150199)
      ·
        refine ⟨1388898184548273201225299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 925932123032182134150199 1388898184548273201225299)
        ·
          refine ⟨2083347276822409801837949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1388898184548273201225299 2083347276822409801837949)
          ·
            refine ⟨781255228808403675689231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2083347276822409801837949 781255228808403675689231)
            ·
              refine ⟨1171882843212605513533847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 781255228808403675689231 1171882843212605513533847)
              ·
                refine ⟨1757824264818908270300771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1171882843212605513533847 1757824264818908270300771)
                ·
                  refine ⟨2636736397228362405451157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1757824264818908270300771 2636736397228362405451157)
                  ·
                    refine ⟨123597018620079487755523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2636736397228362405451157 123597018620079487755523)
                    ·
                      rfl

theorem cell23_722113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_722113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722113 prefixEnd_722113 := by exact prefixLift 722113
  have htrace : WordTrace (prefixWord ++ tailWord_722113) baseStart_722113 baseEnd_722113 := by
    simpa [prefixWord, tailWord_722113, baseEnd_722113] using wordTrace_append hprefix tailTrace_722113
  have hstable : (prefixWord ++ tailWord_722113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722113).length < 2 ^ (prefixWord ++ tailWord_722113).sum := by decide
  have hdescent : baseEnd_722113 < baseStart_722113 := by decide
  rcases family_descends (prefixWord ++ tailWord_722113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722116 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_722116 : Nat := 118140960795 + 722116 * 2 ^ 59
def prefixEnd_722116 : Nat := 4983230072969 + 3 ^ 40 * 722116 * 2
def baseEnd_722116 : Nat := 370792596302201951529055

theorem tailTrace_722116 : CollatzResearch.WordTrace tailWord_722116 prefixEnd_722116 370792596302201951529055 := by
  unfold tailWord_722116
  simp only [CollatzResearch.WordTrace]
  refine ⟨13168867125952267219649101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17558489501269689626198801 13168867125952267219649101)
  ·
    refine ⟨4938325172232100207368413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13168867125952267219649101 4938325172232100207368413)
    ·
      refine ⟨1851871939587037577763155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4938325172232100207368413 1851871939587037577763155)
      ·
        refine ⟨2777807909380556366644733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1851871939587037577763155 2777807909380556366644733)
        ·
          refine ⟨1041677966017708637491775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2777807909380556366644733 1041677966017708637491775)
          ·
            refine ⟨1562516949026562956237663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041677966017708637491775 1562516949026562956237663)
            ·
              refine ⟨2343775423539844434356495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1562516949026562956237663 2343775423539844434356495)
              ·
                refine ⟨3515663135309766651534743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2343775423539844434356495 3515663135309766651534743)
                ·
                  refine ⟨5273494702964649977302115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3515663135309766651534743 5273494702964649977302115)
                  ·
                    refine ⟨7910242054446974965953173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5273494702964649977302115 7910242054446974965953173)
                    ·
                      refine ⟨370792596302201951529055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7910242054446974965953173 370792596302201951529055)
                      ·
                        rfl

theorem cell23_722116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_722116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722116 prefixEnd_722116 := by exact prefixLift 722116
  have htrace : WordTrace (prefixWord ++ tailWord_722116) baseStart_722116 baseEnd_722116 := by
    simpa [prefixWord, tailWord_722116, baseEnd_722116] using wordTrace_append hprefix tailTrace_722116
  have hstable : (prefixWord ++ tailWord_722116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722116).length < 2 ^ (prefixWord ++ tailWord_722116).sum := by decide
  have hdescent : baseEnd_722116 < baseStart_722116 := by decide
  rcases family_descends (prefixWord ++ tailWord_722116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722176 : List Nat := [2, 1, 1, 2, 1, 1, 3, 5, 1, 4, 2]
def baseStart_722176 : Nat := 118140960795 + 722176 * 2 ^ 59
def prefixEnd_722176 : Nat := 4983230072969 + 3 ^ 40 * 722176 * 2
def baseEnd_722176 : Nat := 370823405141471716778779

theorem tailTrace_722176 : CollatzResearch.WordTrace tailWord_722176 prefixEnd_722176 370823405141471716778779 := by
  unfold tailWord_722176
  simp only [CollatzResearch.WordTrace]
  refine ⟨13169961315843582343241191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17559948421124776457654921 13169961315843582343241191)
  ·
    refine ⟨19754941973765373514861787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13169961315843582343241191 19754941973765373514861787)
    ·
      refine ⟨29632412960648060272292681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19754941973765373514861787 29632412960648060272292681)
      ·
        refine ⟨22224309720486045204219511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29632412960648060272292681 22224309720486045204219511)
        ·
          refine ⟨33336464580729067806329267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22224309720486045204219511 33336464580729067806329267)
          ·
            refine ⟨50004696871093601709493901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33336464580729067806329267 50004696871093601709493901)
            ·
              refine ⟨18751761326660100641060213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50004696871093601709493901 18751761326660100641060213)
              ·
                refine ⟨1757977624374384435099395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18751761326660100641060213 1757977624374384435099395)
                ·
                  refine ⟨2636966436561576652649093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1757977624374384435099395 2636966436561576652649093)
                  ·
                    refine ⟨494431206855295622371705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2636966436561576652649093 494431206855295622371705)
                    ·
                      refine ⟨370823405141471716778779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 494431206855295622371705 370823405141471716778779)
                      ·
                        rfl

theorem cell23_722176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 1, 4, 2].length) (baseStart_722176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722176 prefixEnd_722176 := by exact prefixLift 722176
  have htrace : WordTrace (prefixWord ++ tailWord_722176) baseStart_722176 baseEnd_722176 := by
    simpa [prefixWord, tailWord_722176, baseEnd_722176] using wordTrace_append hprefix tailTrace_722176
  have hstable : (prefixWord ++ tailWord_722176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722176).length < 2 ^ (prefixWord ++ tailWord_722176).sum := by decide
  have hdescent : baseEnd_722176 < baseStart_722176 := by decide
  rcases family_descends (prefixWord ++ tailWord_722176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722179 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 5]
def baseStart_722179 : Nat := 118140960795 + 722179 * 2 ^ 59
def prefixEnd_722179 : Nat := 4983230072969 + 3 ^ 40 * 722179 * 2
def baseEnd_722179 : Nat := 370824945583435205041265

theorem tailTrace_722179 : CollatzResearch.WordTrace tailWord_722179 prefixEnd_722179 370824945583435205041265 := by
  unfold tailWord_722179
  simp only [CollatzResearch.WordTrace]
  refine ⟨26340032050676296198841591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17560021367117530799227727 26340032050676296198841591)
  ·
    refine ⟨39510048076014444298262387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26340032050676296198841591 39510048076014444298262387)
    ·
      refine ⟨59265072114021666447393581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39510048076014444298262387 59265072114021666447393581)
      ·
        refine ⟨22224402042758124917772593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59265072114021666447393581 22224402042758124917772593)
        ·
          refine ⟨16668301532068593688329445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22224402042758124917772593 16668301532068593688329445)
          ·
            refine ⟨3125306537262861316561771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16668301532068593688329445 3125306537262861316561771)
            ·
              refine ⟨4687959805894291974842657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3125306537262861316561771 4687959805894291974842657)
              ·
                refine ⟨3515969854420718981131993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4687959805894291974842657 3515969854420718981131993)
                ·
                  refine ⟨2636977390815539235848995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3515969854420718981131993 2636977390815539235848995)
                  ·
                    refine ⟨3955466086223308853773493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2636977390815539235848995 3955466086223308853773493)
                    ·
                      refine ⟨370824945583435205041265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3955466086223308853773493 370824945583435205041265)
                      ·
                        rfl

theorem cell23_722179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_722179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_722179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_722179 prefixEnd_722179 := by exact prefixLift 722179
  have htrace : WordTrace (prefixWord ++ tailWord_722179) baseStart_722179 baseEnd_722179 := by
    simpa [prefixWord, tailWord_722179, baseEnd_722179] using wordTrace_append hprefix tailTrace_722179
  have hstable : (prefixWord ++ tailWord_722179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722179).length < 2 ^ (prefixWord ++ tailWord_722179).sum := by decide
  have hdescent : baseEnd_722179 < baseStart_722179 := by decide
  rcases family_descends (prefixWord ++ tailWord_722179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
